"""Empirical checks for the Python modem quine.

    python3 check.py [file.py]

The default file is modem.py in this folder, written by `lake exe quine`. With it comes
modem.txt, the frames that Lean's `render` predicts: one line of ten bits per byte, start bit
first.

Each program runs with a stand-in for `miniaudio`, whose playback device drains the program's
generator and keeps the samples, and with `time.sleep` made a no-op. No sound is played, and
miniaudio need not be installed.
The samples are then demodulated in two ways:
- by this script, bit by bit, comparing the energy at the mark and space frequencies;
- by minimodem, an independent software modem, if it is installed (`minimodem --rx 300`).
"""

import array
import math
import os
import random
import shutil
import subprocess
import sys
import tempfile
import time
import types
import wave

HERE = os.path.dirname(os.path.abspath(__file__))
RATE, BAUD, MARK, SPACE = 48000, 300, 1270, 1070
N = RATE // BAUD                                    # samples per bit
LEAD_IN, LEAD_OUT = 300, 150                        # mark bits before and after the message
with open(os.path.join(HERE, 'modem.py.inc'), encoding='ascii') as f:
    LIB = f.read()


class Device:
    """Stands in for `miniaudio.PlaybackDevice`: it drains the generator and keeps the samples."""

    def __init__(self, **settings):
        self.settings, self.data = settings, b''

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        return False

    def start(self, generator):
        # ask for 1000 frames at a time, as the real device does, until the generator gives none
        while chunk := bytes(generator.send(1000)):
            self.data += chunk


def record(source):
    """Run a program; return its device settings and the samples."""
    devices = []
    stub = types.ModuleType('miniaudio')
    stub.PlaybackDevice = lambda **k: devices.append(Device(**k)) or devices[-1]
    saved, sleep = sys.modules.get('miniaudio'), time.sleep
    sys.modules['miniaudio'], time.sleep = stub, lambda seconds: None
    try:
        exec(compile(source, 'quine', 'exec'), {'__name__': '__main__'})
    finally:
        time.sleep = sleep
        if saved is not None:
            sys.modules['miniaudio'] = saved
        else:
            del sys.modules['miniaudio']
    if len(devices) != 1:
        raise SystemExit('the program must open exactly one playback device')
    samples = array.array('h')
    samples.frombytes(devices[0].data)
    return devices[0].settings, samples


def power(x, f):
    """The energy of `x` at frequency `f`."""
    w = 2 * math.pi * f / RATE
    re = sum(v * math.cos(w * n) for n, v in enumerate(x))
    im = sum(v * math.sin(w * n) for n, v in enumerate(x))
    return re * re + im * im


def demodulate(samples):
    """The bits: for each bit period, mark (1) if its energy at the mark frequency is higher."""
    if len(samples) % N:
        raise SystemExit('the sound is not a whole number of bits')
    return [int(power(samples[i:i + N], MARK) > power(samples[i:i + N], SPACE))
            for i in range(0, len(samples), N)]


def frames(bits):
    """Split the bits into the lead-in, the 8N1 frames and the lead-out."""
    if bits[:LEAD_IN] != [1] * LEAD_IN or bits[-LEAD_OUT:] != [1] * LEAD_OUT:
        raise SystemExit('the message does not start and end with mark tone')
    body = bits[LEAD_IN:-LEAD_OUT]
    if len(body) % 10:
        raise SystemExit('the message is not a whole number of frames')
    out = [body[i:i + 10] for i in range(0, len(body), 10)]
    for w in out:
        if w[0] != 0 or w[9] != 1:
            raise SystemExit('a frame without its start or stop bit')
    return out


def read(fs):
    return bytes(sum(b << i for i, b in enumerate(w[1:9])) for w in fs).decode('ascii')


def minimodem(samples):
    """Decode the samples with minimodem; None if it is not installed."""
    exe = shutil.which('minimodem')
    if exe is None:
        return None
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, 'modem.wav')
        with wave.open(path, 'wb') as w:
            w.setnchannels(1)
            w.setsampwidth(2)
            w.setframerate(RATE)
            w.writeframes(samples.tobytes())
        r = subprocess.run([exe, '--rx', '-q', '-f', path, str(BAUD)], capture_output=True)
        return r.stdout.decode('latin1')


def quoted(t):
    """Lean's `quoteWith`: a file that binds `t`, in hexadecimal, to `v` and plays it."""
    return ('v=bytes.fromhex("' + t.encode().hex() + '").decode();exec("""' + LIB
            + 'play(v)""")\n')


def check_library():
    rng = random.Random(1)
    every = ''.join(map(chr, range(128)))
    tests = [every, every[::-1], 'e']
    for _ in range(5):
        tests.append(''.join(rng.choice(every) for _ in range(rng.randrange(1, 200))))
    settings, by_mm = None, 0
    for t in tests:
        settings, samples = record(quoted(t))
        if read(frames(demodulate(samples))) != t:
            raise SystemExit(f'library: the sound of {t!r} does not decode to it')
        mm = minimodem(samples)
        if mm is not None:
            if mm != t:
                raise SystemExit(f'library: minimodem decodes the sound of {t!r} as {mm!r}')
            by_mm += 1
    # miniaudio's default output format is signed 16-bit
    if settings != {'nchannels': 1, 'sample_rate': RATE}:
        raise SystemExit(f'unexpected device settings {settings}')
    print(f'library: {len(tests)} texts, including every ASCII character, play their own frames'
          + (f'; minimodem agrees on all {by_mm}' if by_mm else ''))


def check_quine(path):
    with open(path, encoding='ascii') as f:
        source = f.read()
    _, samples = record(source)
    fs = frames(demodulate(samples))
    predicted = os.path.join(os.path.dirname(path), 'modem.txt')
    if os.path.exists(predicted):
        with open(predicted, encoding='ascii') as f:
            if ''.join(''.join(map(str, w)) + '\n' for w in fs) != f.read():
                raise SystemExit(f'{path}: the frames differ from modem.txt (Lean)')
        print(f'{path}: the frames are modem.txt, as Lean predicts')
    if read(fs) != source:
        raise SystemExit(f'{path}: the sound does not decode to the source')
    print(f'{path}: {len(source)} bytes play for {len(samples) / RATE:.0f} s and decode to the '
          'source')
    mm = minimodem(samples)
    if mm is None:
        print('minimodem is not installed; skipped the independent decoder')
    elif mm != source:
        raise SystemExit(f'{path}: minimodem decodes the sound differently ({len(mm)} bytes)')
    else:
        print(f'{path}: minimodem decodes the sound to the source')


check_library()
check_quine(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'modem.py'))
