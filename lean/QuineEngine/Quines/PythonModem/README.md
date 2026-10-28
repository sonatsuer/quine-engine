# A Python program that plays itself as a modem

A Python program that plays its own source as the sound of a 300-baud modem, through the speaker.
It prints nothing.

| File | Contents |
| --- | --- |
| `PythonModem.lean` | the instance of the engine and the proof |
| `modem.py.inc` | the Python library embedded in the program (a fragment, not a program) |
| `check.py` | runs the files with a stand-in for `miniaudio` and demodulates the sound |
| `modem.py` | the quine, written by `lake exe quine` |
| `modem.txt` | the frames that the Lean model predicts, written by `lake exe quine` |

## The format

**The modem.** Bell 103, the originate side. This is the classic dial-up sound.
- A mark (1) is a tone of 1,270 Hz, and a space (0) is a tone of 1,070 Hz.
- The tones are phase-continuous, at 300 baud. At 48,000 samples a second, a bit is 160 samples.

**The frames.** Each byte is sent as an 8N1 frame: a start bit 0, the eight data bits
least significant first, and a stop bit 1.

**The lead-in and lead-out.** The message starts after 1 s of mark tone, so that a receiver can
detect the carrier. It ends with 0.5 s of mark tone.

## The file

`modem.py` is 1,154 bytes. It has the shape of the Python braille and Morse quines:

```
v="""# this program plays its own source as a 300-baud modem (bell 103), with miniaudio
import array, math, miniaudio, time
...
play('v='+chr(34)+chr(34)+chr(34)+v+chr(34)+chr(34)+chr(34)+';exec(v)'+chr(10))""";exec(v)
```

**What it does.**
- `play` turns the text into bits, and the bits into 16-bit samples.
- It plays them with [miniaudio](https://github.com/irmen/pyminiaudio), whose wheels include the
  miniaudio C library, so no system audio package is needed. A generator `feed` gives the playback
  device the frames it asks for, and the program waits until the sound has played.

**Running it.** It needs miniaudio 1.71, from pip. Install it into the virtual environment `.venv`
at the repository root, from the root `requirements.txt` (see the root README):

```sh
cd ../../../..                        # the repository root
python3 -m venv .venv
.venv/bin/pip install -r requirements.txt
.venv/bin/python lean/QuineEngine/Quines/PythonModem/modem.py
```

It plays for about 40 s.

**Reading it back.** In another terminal, run
[minimodem](http://www.whence.com/minimodem/) on the microphone:

```sh
minimodem --rx 300
```

When the program plays, minimodem prints its source.

## The development

- **Reuse.** The file model is `lean/QuineEngine/PyScript.lean`, the same as for the Python
  braille and Morse quines, with the library call `play(…)`.
- **The framing.** `lean/QuineEngine/Uart.lean`, shared with the Verilog quine, defines `cell`,
  the frame of a character, and its inverse `uncell`. The proof that `uncell` inverts `cell` is
  computed over the 128 ASCII characters.
- **The representation** is the sequence of frames, one per byte. The tones that realize it are
  part of the trusted library.
- **Result.** `quine_correct : system.IsQuine quine`. It has no hypotheses and depends only on
  `propext` and `Quot.sound`.

**What is trusted:**
1. Python runs files of the modelled shape as modelled;
2. the function `play` in `modem.py.inc` plays the frames that `render` gives as the tones above.

## Testing

Tested with Python 3.12.3. Neither miniaudio nor a sound card is needed. minimodem is optional; no version of it was tested. From this folder:

```sh
python3 check.py
```

The script runs each program with a stand-in for `miniaudio`, whose playback device drains the
program's generator and keeps the samples, and with `time.sleep` made a no-op. It then demodulates them bit by bit, comparing the energy at the two frequencies.
- **The library.** Texts that include every ASCII character, bound in hexadecimal as in Lean's
  `quoteWith`, play their own frames.
- **The quine.** The frames of `modem.py` are those in `modem.txt`, as Lean predicts, and they
  decode to the source.
- **An independent decoder.** If minimodem is installed, the script
  also decodes every sound with it, and the result must be the text.
