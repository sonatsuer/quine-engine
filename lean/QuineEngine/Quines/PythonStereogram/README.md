# A Python program that hides itself in autostereograms

A Python program that writes `stereogram.pdf`: a title page, then pages of random-dot
autostereograms ("magic eye" pictures). Hidden in them, as raised characters, is the program's
own source.

| File | Contents |
| --- | --- |
| `PythonStereogram.lean` | the instance of the engine, the 16-segment table, and the proof |
| `gen_stereogram.py` | writes `font16.txt`, and `stereogram.py.inc` from `stereogram.py.in` |
| `font16.txt` | the 16-segment table: each character and its segments |
| `stereogram.py.in`, `stereogram.py.inc` | the library, before and after the table is filled in |
| `check.py` | runs the files, parses the PDF, and verifies every page |
| `stereogram.py` | the quine, written by `lake exe quine` |
| `stereogram.txt` | the segments that the Lean model predicts, written by `lake exe quine` |
| `stereogram.pdf` | what `stereogram.py` writes: a title page and 140 stereogram pages, 49.5 MB |

## Viewing

Run `python3 stereogram.py`. It takes about 90 s and writes `stereogram.pdf`: 141 pages of
1900 × 1000 px, about 49.5 MB. Open it at 100% zoom (actual size), so that a dot of the picture is a pixel of a
96-dpi screen.

On each page, look *through* the screen (wall-eyed) at the two black dots at the top until you see
three. Then move your gaze down: three rows of eight characters stand out of the dots. Read the
pages in order, row by row.
- **A line break** is a filled cell.
- **A space** is an empty one.
- **Moiré.** Some viewers show moiré patterns at exactly 100%; zooming in a little removes them.

## The format

**The characters** are 16-segment characters, like those of old alphanumeric displays: 140 ×
220 px, with bars 26 px wide.
- **Segments.** There are the top and bottom bars in halves, the sides and the centre bar in
  upper and lower halves, the middle bar in halves, and the four diagonals to the centre.
- **No case.** The characters have no case, so the program has no capital letters. Its letters are
  drawn with the capital shapes. It writes the capitals that PDF needs with a small helper `u`,
  in which `^x` stands for `X`.
- **The table** covers the letters, the digits, the space, the line break, and the punctuation
  that the program uses: 62 characters. Each has its own pattern, and the shapes that usually look
  alike are kept apart: `0` is slashed, and `s` has a diagonal.

**The pages** hold 3 rows of 8 characters, 200 px apart in rows 300 px apart. Each character is
moved by up to 48 × 24 px, by a fixed rule (`i*37 % 49`, `i*23 % 25` for character `i`), so that
the characters never line up with the dots' period.

**The stereogram** uses the algorithm of Thimbleby, Inglis and Witten (*Displaying 3D images:
algorithms for single-image random-dot stereograms*, 1994).
- **Links.** Each dot is linked to its partner half a separation away on each side, and linked
  dots share a colour. The separation is 140 px on the flat background and 112 px on the raised
  characters.
- **Hidden surfaces.** A flat point within 15 px of a raised one is left unlinked, since one eye
  cannot see it. This removes the echoes that otherwise appear beside raised edges.
- **Colours.** There are 256 random colours, drawn as a palette.
- **Guide dots.** Two black dots one separation apart at the top of each page help to fuse it.

**The PDF** is written with `zlib` alone. Each page is one image, with no predictor, at 0.75 pt a
pixel.

## How the format was chosen

The format came from eye tests:
- **A 5 × 7 pixel font** was illegible, even large and bold: thin strokes don't survive stereo
  vision.
- **QR codes** failed: their modules are too small and too irregular.
- **Seven-segment digits** read well, once each digit was jittered off the grid and the hidden
  surfaces were removed.
- **Sixteen segments** read as well.

The cost is bandwidth: 24 characters a page.

## The development

- **The file model** is `lean/QuineEngine/PyScript.lean`, the same as for the braille, Morse and
  modem quines, with the library call `draw(…)`.
- **The representation** is the sequence of segment patterns, one per character. `cell` and
  `uncell` are read from `font16.txt`, and the proof that `uncell` inverts `cell` is computed over
  the table.
- **Result.** `quine_correct : system.IsQuine quine`. It has no hypotheses and depends only on
  `propext` and `Quot.sound`.

**What is trusted:**
1. Python runs files of the modelled shape as modelled;
2. the function `draw` in `stereogram.py.inc` draws the patterns that `render` gives, in this
   layout, as autostereograms, after a title page.

## Testing

Tested with Python 3.12.3, with no extra packages. From this folder:

```sh
python3 check.py
```

The script runs each program, which writes a PDF, and parses the PDF.
- **The title page** comes first and says `I am a Quine`.
- **The links.** From the predicted segments, the script rebuilds each page's depth map with its
  own copy of the layout. It checks that every link holds: the two dots around each point have the
  same colour.
- **The reading.** In each character's cell, from the dots alone, a segment reads as raised when
  its 112 px pairs match more often than its 140 px pairs. The segments read this way must be the
  predicted ones, and they decode to the source.
- **The library.** Texts with every character of the table, bound in hexadecimal as in Lean's
  `quoteWith`, pass the same checks.
