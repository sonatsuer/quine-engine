# An SVG file that draws its own source text

An SVG file whose script draws the file's own source text as pixels. Reading the pixels back with
the font gives the file, character for character. This is the closest visual analogue of an
ordinary quine: the output is a picture of the source, and the scanner is a font-based reader.

| File | Contents |
| --- | --- |
| `SvgText.lean` | the typesetting and scanning, the instance of the engine, and the proof |
| `font5x7.txt` | the 5×7 pixel font, read by both Lean and `check.mjs` |
| `drawtext.js.inc` | the JavaScript renderer embedded in the file (a fragment, not a document) |
| `gen_drawtext.py` | generates `drawtext.js.inc` from `font5x7.txt` |
| `check.mjs` | tests the renderer and the file |
| `text.svg` | the quine, written by `lake exe quine` |
| `expected.pbm` | Lean's own typesetting of the quine, written by `lake exe quine` |

## The file

`text.svg` is 1,178 bytes. When opened in a browser it draws its source text in 15 rows of 80
characters, a 480 × 120 pixel picture. Like the QR quines, it draws with a script, so viewers that
do not run scripts show it blank.

The font is the 5×7 font of the X11 misc-fixed family, which is public domain ("Public domain
font. Share and enjoy."). `font5x7.txt` holds its 95 printable ASCII glyphs. They are pairwise
distinct, for instance `0` and `O`, or `1`, `l` and `|`, and only the space is blank.

## The development

**Typesetting and scanning.** This is the part proved in full here.

- **Pictures.** A picture is a finite `Bitmap`.
- **`typeset t`.** Character `i` of `t` goes in cell `(i % 80, i / 80)`, as a 5×7 glyph in a 6×8
  cell.
- **`decode`.** It reads every cell back with the font (`decodeCell`) and drops trailing spaces.
- **`decode_typeset`.** It proves that `decode (typeset t) = t` for every well-formed `t`: nonempty,
  printable ASCII, and not ending in a space. The restriction is needed because a space is blank.
- **Font facts.** Every glyph decodes to its own character (`decodeGlyph_glyph`), and the blank
  glyph decodes to a space. Both are checked by `decide +kernel`.

**The file and its semantics** come from `lean/QuineEngine/SvgScript.lean`, shared with the SVG
QR quine.

- **Shape.** The file is `<svg …><script>v="x";eval(arg)</script></svg>`, with the evaluated code
  `ENC;drawText(E)`.
- **Display.** A file displays as the typesetting of the value of `E`, if that value is well
  formed.
- **Substitution and template.** Both are the shared ones: `sub` with the `eval(v)` diagonal, and
  `tmplExpr`, which builds `sub v v`.
- **Quotation.** `quote t` binds an escaped `t` and draws it; its domain is the well-formed texts.

**Result.** `quine_correct : system.IsQuine quine`, obtained from `Diagonal.isQuine`.

- There is no capacity bound and no codec parameter: the picture grows with the text, and the
  scanner is defined and proved in Lean.
- The theorem depends only on `propext` and `Quot.sound`; in particular it does not use the axiom
  of choice.

## What the model trusts

1. Browsers run the modelled JavaScript fragment as modelled.
2. `drawtext.js.inc` draws exactly `typeset`.
3. XML passes the script text through unchanged.

Item 2 replaces the QR quines' trusted codec, and `check.mjs` tests it.

## Testing

Tested with Node.js 18.19.1 and npm 9.2.0; no npm packages are needed. From this folder:

```sh
node check.mjs
```

It runs the script with a stub `document` and turns the drawn path back into pixels. Then it checks
three things:
1. for 40 random texts, the renderer draws exactly the reference typesetting computed from
   `font5x7.txt`;
2. the drawing of `text.svg` equals `expected.pbm`, Lean's typesetting of the quine;
3. reading the drawing back gives `text.svg`.

To change the font, edit `font5x7.txt`, run `python3 gen_drawtext.py`, then rebuild and rerun the
checks.
