# A Python program that blinks itself in Morse code

A Python program that opens a window and blinks its own source in Morse code: the window turns
white for light and black for dark. It prints nothing.

| File | Contents |
| --- | --- |
| `PythonMorse.lean` | the instance of the engine, the Morse code, and the proof |
| `morse.py.inc` | the Python library embedded in the program (a fragment, not a program) |
| `check.py` | runs the files with a stand-in for tkinter and decodes the light |
| `morse.py` | the quine, written by `lake exe quine` |
| `morse.txt` | the Morse code that the Lean model predicts, written by `lake exe quine` |

## The format

**The code.** International Morse code (ITU-R M.1677-1), with three additions in common use:
`!` (`-.-.--`), `$` (`...-..-`) and `_` (`..--.-`).

**Timing.**
- A dot is one unit of light (60 ms, about 20 words a minute) and a dash three.
- Gaps are one unit inside a letter and three between letters.
- Each space adds four units, so a single space gives the usual seven-unit gap between words.

**Line breaks** are sent as the prosign AA (`.-.-`).

**Framing.** The message starts with KA (`-.-.-`, the starting signal) and ends with SK
(`...-.-`, end of work), after a two-second dark wait. AR would be the usual ending, but its code
is the same as `+`.

**The alphabet.** Morse code has no case and few symbols, so the program is written in the 57
characters that have codes:
- lower-case letters and digits;
- `. , ? ! / ( ) & : ; = + - _ $ @ " '`;
- the line break and the space.

The program does without capitals, brackets, braces, `*`, `<`, `>`, `#` and the backslash. For
example, its comments are string statements, and it gets `tkinter.Tk` as
`getattr(tkinter,'tk'.capitalize())`.

## The file

`morse.py` is 1,339 bytes. It has the shape of the Python braille quine:

```
v="""'this program blinks its own source in morse code, in a window'
import tkinter
...
blink('v='+chr(34)+chr(34)+chr(34)+v+chr(34)+chr(34)+chr(34)+';exec(v)'+chr(10))""";exec(v)
```

**What it does.**
- `blink` turns the text into a schedule of light and dark.
- It opens a 300 × 300 window and steps through the schedule with tkinter's `after`.
- It closes the window at the end.

**Running it.** `python3 morse.py` blinks for about 17 minutes. It needs tkinter, with Tk 8.6.14. You can read it by eye, or record
it with a camera and decode the video.

## The development

- **Reuse.** The file model is `lean/QuineEngine/PyScript.lean`, the same as for the Python
  braille quine, with the library call `blink(…)`.
- **The Morse code.** `PythonMorse.lean` defines it (`cell`) and its inverse (`uncell`). The
  proof that `uncell` inverts `cell` is computed over the 57 characters.
- **The representation** is the sequence of codes, one per character, with the empty code for a
  space. The timing that realizes it is part of the trusted library.
- **Result.** `quine_correct : system.IsQuine quine`. It has no hypotheses and depends only on
  `propext` and `Quot.sound`.

**What is trusted:**
1. Python runs files of the modelled shape as modelled;
2. the function `blink` in `morse.py.inc` blinks the codes that `render` gives, with the timing
   above.

## Testing

Tested with Python 3.12.3, with no extra packages and no display. From this folder:

```sh
python3 check.py
```

**The stand-in.** The script runs each file with a stand-in for tkinter. It records the window's
colour changes and the delays between them on a virtual clock, so the 17 minutes pass at once.
It then decodes the light by timing alone.

The script checks:
- **The library.** The quotation files for several texts, including every character, runs of
  spaces and line breaks, blink codes that decode back to the texts.
- **The quine against Lean.** The blinking of `morse.py` is `morse.txt`, the prediction of the
  Lean model.
- **The quine against itself.** The blinking decodes to the source.

**What is not tested:** the stand-in is not tkinter. A real tkinter window was opened briefly to
check that the program runs, but the window's timing was not measured.
