"""Empirical checks for the Python spectrogram quine.

    python check.py [file.py]       fuzz the library, then check the quine
    python check.py --fuzz          fuzz the library only
    python check.py --decode a.wav  decode the spectrogram of a recording

Run it with the Python of the virtual environment, which has numpy, Pillow and zxing-cpp:
`../../../../.venv/bin/python check.py`. The programs themselves run with `python3`.

The default file is spectrogram.py in this folder, written by `lake exe quine`. Each program is run
with `-w`, which writes a WAV to stdout. The check draws two spectrograms of the sound, as gray
images with loud as light, and decodes both with zxing-cpp:
- its own: a Hann window of 4096 samples, 40 columns a second, 6.25 Hz a row and 40 dB of range,
  so that a module is 8 x 8 pixels;
- sox's (`sox ... spectrogram`), at 4 x 4 pixels a module.
The quine is also run without the flag, with a stand-in for miniaudio that captures what it
plays; it must be the samples of the WAV. The quine's sound and its spectrogram are written to
spectrogram.wav and spectrogram.png.
"""

import io
import os
import random
import shutil
import subprocess
import sys
import tempfile
import wave

import numpy as np
import zxingcpp
from PIL import Image

HERE = os.path.dirname(os.path.abspath(__file__))
ENC = open(os.path.join(HERE, 'spectrogram.py.inc'), encoding='latin1').read()
CAPACITY = 2953
WORK = tempfile.mkdtemp(prefix='spectrogram-quine-')

# A stand-in for miniaudio: the playback device drains the program's generator and appends the
# samples to $MINIAUDIO_OUT, and time.sleep becomes a no-op.
with open(os.path.join(WORK, 'miniaudio.py'), 'w') as f:
    f.write('''import os, time
time.sleep = lambda seconds: None
class PlaybackDevice:
    def __init__(self, **settings):
        assert settings == {'nchannels': 1, 'sample_rate': 48000}
    def __enter__(self):
        return self
    def __exit__(self, *a):
        pass
    def start(self, generator):
        with open(os.environ['MINIAUDIO_OUT'], 'ab') as f:
            while chunk := bytes(generator.send(1000)):
                f.write(chunk)
''')


def run_wav(path):
    """Run a program with -w; the WAV bytes, or None if it fails."""
    r = subprocess.run(['python3', path, '-w'], capture_output=True)
    return r.stdout if r.returncode == 0 else None


def run_play(path):
    """Run a program without arguments and the stand-in miniaudio; the bytes it plays."""
    out = os.path.join(WORK, 'played.raw')
    open(out, 'wb').close()
    env = dict(os.environ, PYTHONPATH=WORK, MINIAUDIO_OUT=out)
    subprocess.run(['python3', path], env=env, check=True, capture_output=True)
    return open(out, 'rb').read()


def read_wav(data):
    """The rate and the first channel, as floats, of a 16-bit WAV."""
    with wave.open(io.BytesIO(data)) as w:
        if w.getsampwidth() != 2:
            raise SystemExit('only 16-bit WAV files are supported')
        x = np.frombuffer(w.readframes(w.getnframes()), '<i2')
        return w.getframerate(), x[::w.getnchannels()] / 32768


def spectrogram(rate, x, fps=40, hz=6.25, top=10500, win=4096, rng=40):
    """A gray image: columns at fps a second (from 0.25 s before the sound to 0.25 s after it), rows
    of hz from top down to 0 Hz, and the top rng dB of the magnitude."""
    win = round(win * rate / 48000)
    nfft = 1 << (4 * win - 1).bit_length()
    hop, pad = rate / fps, round(0.25 * fps)
    cols = int(np.ceil(len(x) / hop)) + 2 * pad
    x = np.concatenate([np.zeros(win), x, np.zeros(win + int(2 * pad * hop))])
    starts = (np.round((np.arange(cols) - pad) * hop - win / 2) + win).astype(int)
    frames = x[starts[:, None] + np.arange(win)] * np.hanning(win)
    mag = np.abs(np.fft.rfft(frames, nfft))
    f = (top - (np.arange(int(top / hz)) + 0.5) * hz) * nfft / rate
    db = 20 * np.log10(np.stack([np.interp(f, np.arange(mag.shape[1]), m) for m in mag], 1) + 1e-12)
    return Image.fromarray(np.clip((db - db.max() + rng) / rng * 255, 0, 255).astype(np.uint8))


def sox_spectrogram(wav_bytes):
    """sox's spectrogram, 4 x 4 pixels a module: at 21 kHz, 841 rows of 12.5 Hz and 20 columns a
    second."""
    w, p = os.path.join(WORK, 'sox.wav'), os.path.join(WORK, 'sox.png')
    open(w, 'wb').write(wav_bytes)
    subprocess.run(['sox', w, '-n', 'rate', '21k', 'spectrogram', '-m', '-r', '-Z', '-40', '-z', '40',
                    '-y', '841', '-X', '20', '-o', p], check=True)
    return Image.open(p).convert('L')


def decode(img):
    """The texts of the QR codes that zxing-cpp finds in an image."""
    return [r.bytes.decode('latin1') for r in zxingcpp.read_barcodes(img, formats=zxingcpp.BarcodeFormat.QRCode)]


def check_image(label, img, expected):
    if decode(img) != [expected]:
        raise SystemExit(f'{label}: the spectrogram does not decode to the text')


HAS_SOX = shutil.which('sox') is not None


def program(t):
    """Lean's `quoteWith`: bind t, in hexadecimal, to v, and run the library on v."""
    return 'v=bytes.fromhex("' + t.encode('latin1').hex() + '").decode();exec("""' + ENC + 'play(v)""")\n'


def fuzz():
    # zxing-cpp reads no QR code of the empty text (from segno either), so the lengths start at 1
    lengths = [1, 1000, CAPACITY - 1, CAPACITY] + [random.randrange(CAPACITY + 1) for _ in range(2)]
    for n in lengths:
        t = ''.join(chr(i) if i < 128 else chr(random.randrange(128)) for i in range(n))
        path = os.path.join(WORK, 'fuzz.py')
        open(path, 'w', encoding='latin1').write(program(t))
        wav = run_wav(path)
        if wav is None:
            raise SystemExit(f'fuzz length {n}: the program failed')
        check_image(f'fuzz length {n}', spectrogram(*read_wav(wav)), t)
        if HAS_SOX:
            check_image(f'fuzz length {n} (sox)', sox_spectrogram(wav), t)
    path = os.path.join(WORK, 'over.py')
    open(path, 'w').write(program('x' * (CAPACITY + 1)))
    if run_wav(path) is not None:
        raise SystemExit('fuzz: the library accepted a text above capacity')
    drawn = 'its own spectrogram and sox' + "'" + 's' if HAS_SOX else 'its own spectrogram'
    print(f'library: {len(lengths)} texts, including every ASCII character, decode from {drawn}; overflow rejected')


def check_quine(path, write):
    src = open(path, encoding='latin1').read()
    wav = run_wav(path)
    if wav is None:
        raise SystemExit(f'{path}: the program failed')
    with wave.open(io.BytesIO(wav)) as w:
        if (w.getframerate(), w.getnchannels(), w.getsampwidth()) != (48000, 1, 2):
            raise SystemExit(f'{path}: not a 48 kHz mono 16-bit WAV')
        raw = w.readframes(w.getnframes())
    if run_play(path) != raw:
        raise SystemExit(f'{path}: it plays other samples than it writes')
    img = spectrogram(*read_wav(wav))
    check_image(path, img, src)
    print(f'{path}: {len(raw) / 96000:.1f} s of sound, played and written alike; zxing-cpp decodes its spectrogram to the source')
    if HAS_SOX:
        check_image(f'{path} (sox)', sox_spectrogram(wav), src)
        print(f'{path}: zxing-cpp decodes the spectrogram that sox draws to the source')
    else:
        print('sox: skipped (not installed; sudo apt install sox)')
    if write:
        open(os.path.join(HERE, 'spectrogram.wav'), 'wb').write(wav)
        img.save(os.path.join(HERE, 'spectrogram.png'))


def decode_recording(path):
    img = spectrogram(*read_wav(open(path, 'rb').read()))
    out = os.path.join(HERE, 'notrack-recording.png')
    img.save(out)
    src = open(os.path.join(HERE, 'spectrogram.py'), encoding='latin1').read()
    texts = decode(img)
    if not texts:
        print('no QR code found')
    for t in texts:
        print(f'{len(t)} bytes: ' + ('the source of spectrogram.py' if t == src else 'not the source of spectrogram.py'))
    print(f'the spectrogram is in {out}')


try:
    args = sys.argv[1:]
    if args[:1] == ['--decode']:
        decode_recording(args[1])
    else:
        fuzz()
        if args[:1] != ['--fuzz']:
            check_quine(args[0] if args else os.path.join(HERE, 'spectrogram.py'), not args)
finally:
    shutil.rmtree(WORK, ignore_errors=True)
