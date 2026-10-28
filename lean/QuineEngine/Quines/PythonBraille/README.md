# A Python program that prints itself in braille

A Python program that prints its own source in braille.

| File | Contents |
| --- | --- |
| `PythonBraille.lean` | the instance of the engine, the braille code, and the proof |
| `braille.py.inc` | the Python library embedded in the program (a fragment, not a program) |
| `check.py` | tests the library and the program against a NABCC table from liblouis |
| `braille.py` | the quine, written by `lake exe quine` |
| `braille.txt` | the output that the Lean model predicts, written by `lake exe quine` |

## The format

The output is the North American Computer Braille Code (NABCC), the 8-dot code of refreshable
braille displays, written as Unicode braille cells (U+2800–U+28FF). Each printable ASCII character
has its own cell:

- **Space to `?`** use the 6-dot Braille ASCII cells.
- **`@` to `^`**, which include the capital letters, use the Braille ASCII cell plus dot 7.
- **`_`** uses its Braille ASCII cell without dot 7. This is the exception in the standard;
  liblouis and BRLTTY agree on it.
- **`` ` `` to `~`**, which include the lower-case letters, use the cell of the character 32
  below, without dot 7.

Newlines stay newlines, so each line of the program becomes one line of cells. To read the output
back, replace each cell by its character.

## The file

`braille.py` is 1,191 bytes of readable, multi-line Python:

```
v="""# A Python program that prints itself in braille.
...
braille('v='+chr(34)+chr(34)+chr(34)+v+chr(34)+chr(34)+chr(34)+';exec(v)'+chr(10))""";exec(v)
```

- **The mechanism.** It binds its code to `v` and runs it with `exec`, the literal + eval shape of
  the SVG and PostScript quines.
- **The literal.** The code avoids `"` and backslashes so that it can sit in the `"""…"""` literal.
  It writes `"` and the newline as `chr(34)` and `chr(10)`.
- **Running it.** `python3 braille.py` prints the braille. A terminal font with the braille block,
  such as DejaVu Sans Mono, shows it.

## The development

- The file model is `lean/QuineEngine/PyScript.lean`.
  - **Files** have the shape `v=LIT;exec(ARG)` and a newline, where `ARG` is `v` or a literal.
  - **Literals** are `"""…"""` (printable ASCII and newline, no `"` or backslash) or
    `bytes.fromhex("…").decode()`.
  - **The executed code** is the library followed by `braille(E)`, where `E` is a sum of `'…'`
    literals, `v` and `chr(n)`.
- `PythonBraille.lean` defines NABCC (`cell`) and its inverse (`uncell`). The proof that `uncell`
  inverts `cell` is computed over all 128 ASCII characters.
- **Result.** `quine_correct : system.IsQuine quine`. It has no hypotheses, because the braille
  code is concrete, and it depends only on `propext` and `Quot.sound`.

**What is trusted:**
1. Python runs files of the modelled shape as modelled;
2. the function `braille` in `braille.py.inc` prints `render` of its argument, and the library
   leaves `v` and `chr` alone.

## Testing

Tested with Python 3.12.3, with no extra packages. From this folder:

```sh
python3 check.py
```

The reference is a NABCC table in `check.py`, copied from the table `en-nabcc.utb` of
[liblouis](https://liblouis.io) 3.29.0. The script checks:
- **The library.** `cell` agrees with the table on every printable character and on newline, and
  no two characters share a cell.
- **The program against Lean.** The output of `python3 braille.py` is exactly `braille.txt`, the
  prediction of the Lean model.
- **The program against the table.** The output is the NABCC of the source, and it reads back to
  the source.
