# A Python program whose sound shows its own QR code

A Python program that makes a 37 s sound. In a spectrogram of the sound, the picture is a QR code
of the program's own source, and a phone can scan it.

| File | Contents |
| --- | --- |
| `PythonSpectrogram.lean` | the instance of the engine and the proof |
| `spectrogram.py.inc` | the Python library embedded in the program (a fragment, not a program) |
| `check.py` | runs the files, draws their spectrograms, and decodes them |
| `spectrogram.py` | the quine, written by `lake exe quine` |
| `spectrogram.wav` | the sound of `spectrogram.py`, written by `check.py` (3.6 MB) |
| `spectrogram.png` | its spectrogram, as `check.py` draws it, written by `check.py` |

## Running it

The program uses only the Python standard library to make the sound. It takes about 11 s.

- **Writing a file.** `python3 spectrogram.py -w > s.wav` writes a WAV file: mono, 16-bit, 48 kHz.
  `python3 spectrogram.py -w | aplay` plays it.
- **Playing.** Without the flag, the program plays the sound with
  [miniaudio](https://github.com/irmen/pyminiaudio) 1.71, as the modem quine does; its wheels
  include the audio library, so no system package is needed. Install it into the virtual environment at
  the repository root (`.venv/bin/pip install -r requirements.txt`; see the root README):
  `.venv/bin/python lean/QuineEngine/Quines/PythonSpectrogram/spectrogram.py`.

## Viewing it

Open the WAV in Audacity or Sonic Visualiser and show the spectrogram:
- **Scale:** linear frequency, not logarithmic or mel, so that the rows are equally spaced.
- **Window:** about 4096 samples (85 ms).
- **Range:** about 40 dB.

Scan the screen with a phone. A phone spectrogram app that listens to the speaker also works.

## The format

**The QR code** is version 40, level L, byte mode, mask 0: 177 × 177 modules, for up to 2,953 bytes.
The encoder is written in Python, with no packages; it is a port of the gnuplot quine's encoder. A
fixed version needs no tables, and the program (2,918 bytes) needs version 40 in any case.

**The picture** is the symbol with a quiet zone of 4 modules: 185 × 185 modules.
- **Columns are time.** Each column is 0.2 s.
- **Rows are frequency.** Row y, counted from the top, is centred on 9,700 − 50·y Hz, from 9,700 Hz
  down to 500 Hz.
- **A light module sounds, and a dark one is silent.** Spectrogram viewers draw loud as bright, so
  the picture is a normal QR code on a bright square.

**The sound of a light module** is two tones, 5 Hz below and 5 Hz above the row's centre.
- **Why two tones.** A spectrogram blurs every tone across about two frequency bins.
  - One tone a row makes thin bright lines with dark gaps between the rows, and scanners can't
    read the stripes.
  - Tones that fill the whole row spread into the dark rows next to them.
  - Two tones close to the centre let the blur fill the light rows and leave the dark ones dark.
- **Continuity.** Every tone has a whole number of cycles in a column. So one table of samples a row
  serves every column, and a row that stays on is one continuous tone.
- **Ramps.** A tone rises or falls in 20 ms only where its row turns on or off. A ramp at every
  column made vertical streaks across the picture.
- **Phases.** The starting phases are spread quadratically over the rows, which keeps the peaks of
  the sum low.

The format was chosen by scanning test spectrograms with a phone.
- **Did not scan:** one tone a row (0.1 s and 0.2 s columns), a tone that sweeps across its row,
  and five tones that fill the row.
- **Scanned:** two tones and three tones near the centre of the row.

## The development

- **Reuse.** The file model is `lean/QuineEngine/PyScript.lean`, as for the other Python quines,
  with the library call `play(…)`.
- **The barcode** is the abstract `Codec` of `lean/QuineEngine/Barcode.lean`, as for the other QR
  quines.
- **Result.** `quine_correct (Q : Codec) (hC : 2953 ≤ Q.C) : (system Q).IsQuine quine`. It depends
  only on `propext` and `Quot.sound`. `quine_length` proves that the quine fits version 40-L.

**What is trusted:**
1. Python runs files of the modelled shape as modelled;
2. `play` in `spectrogram.py.inc` makes a sound whose spectrogram is the QR code of its argument,
   for a codec of capacity 2953.

## Testing

Tested with Python 3.12.3 and, in the virtual environment, numpy 2.5.4, Pillow 13.0.0 and zxing-cpp 3.1.1 (pinned in the root `requirements.txt`). sox 14.4.2 is optional. The programs themselves run with `python3`.

```sh
.venv/bin/pip install -r requirements.txt     # at the repository root
cd lean/QuineEngine/Quines/PythonSpectrogram
../../../../.venv/bin/python check.py
```

It takes about 1.5 minutes.
- **Each program** is run with `-w`. Its sound is drawn twice and decoded with
  [zxing-cpp](https://github.com/zxing-cpp/zxing-cpp), the C++ ZXing.
  - **The check's own spectrogram:** a Hann window of 4096 samples, 40 columns a second, 6.25 Hz a
    row and 40 dB of range, so a module is 8 × 8 pixels.
  - **sox's spectrogram:** 4 × 4 pixels a module.
- **The library.** Texts of 1, 1,000, 2,952 and 2,953 bytes and two random lengths, bound in
  hexadecimal as in Lean's `quoteWith`, include every ASCII character. Both spectrograms of each
  decode to the text. A text of 2,954 bytes is rejected.
  - **The empty text is not tested.** zxing-cpp reads no QR code of the empty text, from any
    encoder; segno's fails too.
- **The quine.** Both spectrograms decode to the source. The program is also run without the flag,
  with a stand-in for miniaudio that captures what it plays, and it must play the samples it
  writes. The check then writes `spectrogram.wav` and `spectrogram.png`.
- **A recording.** `check.py --decode rec.wav` draws the spectrogram of a recording, writes it to
  `notrack-recording.png` and decodes it. To record the program through the air:

  ```sh
  arecord -f S16_LE -r 48000 -c 1 -d 40 rec.wav    # in one terminal
  .venv/bin/python spectrogram.py                  # in another
  ```

**Why not jsQR or the JavaScript ZXing**, as in the other QR checks: they were erratic on these
version-40 images, and failed on some that a phone scanned. zxing-cpp agreed with the phone on every
image tried.
