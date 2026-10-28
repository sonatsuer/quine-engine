# A pdfLaTeX file that typesets a color QR code of itself

A `.tex` file whose PDF is a color QR code of the file. The code is drawn as a field of
mathematics: every data cell carries a Greek letter or an operator in a tint of the cell's color.

![A close-up of the code](closeup.png)

| File | Contents |
| --- | --- |
| `LatexQrCode.lean` | the instance of the engine and the proof |
| `encoder-source.tex` | the readable expl3 QR encoder, one statement or block per line |
| `gen_encoder.py` | writes the three fixed pieces below; golfs the expl3 code |
| `pre.inc`, `library.inc`, `epilogue.inc` | the prefix, the library and the template |
| `check.mjs` | compiles files with pdfLaTeX and decodes them with jsQR and ZXing |
| `qr-code.tex` | the quine, written by `lake exe quine` |
| `qr-code.pdf` | its PDF; `preview.png` is the whole page, `closeup.png` the picture above |

## The format

The code follows the convention of the color QR quines, at version 40.
- **Encoding.** The file is split into thirds, of lengths `⌈n/3⌉`, `⌈n/3⌉` and the rest. Each
  third is encoded as a QR code: version 40 (177 × 177 modules), level L, byte mode, mask 0.
- **Overlay.** The three codes share one picture. In each module, the red channel is dark where
  the first code is dark, the green channel where the second code is, and the blue channel where
  the third code is. This gives eight colors.
- **Scanning.** Separate the three channels, decode each one as an ordinary QR code, and
  concatenate the payloads.
- **Capacity.** The capacity is 3 × 2,953 = 8,859 bytes. The file is 6,430 bytes.

This is a research convention, not a standard barcode: an ordinary scanner reads one channel's
worth at most.

## The look

Each module is a 2.6 pt cell.
- **The fill.** A cell is filled with its color. A dark channel has value 0, and a light channel
  has value 1.
- **The symbols.** A data cell also carries a symbol: a Greek letter or an operator
  (`α β γ δ π σ φ ψ ω θ λ μ ∂ ∞ ⊕ ⊗`), cycled by position.
  - The glyphs are `\char`s of the `cmmi` and `cmsy` fonts.
  - A symbol is drawn in a tint of its cell's color. A dark channel has value 0.3 and a light
    channel 0.82, so in every channel the symbol stays on the same side of 50% as its cell.
- **Function modules** (finders, timing, format and version information, alignment) carry no
  symbol, so the patterns a scanner needs to find are clean.

## The file

`qr-code.tex` is one line, with the shape

```
PRE  x  |
```

- **`PRE`** sets up the page and defines `\grab`. It then sets the special characters to catcode
  12 and starts `\grab` with `\afterassignment`, once backslash itself is at catcode 12. So
  `\grab` reads the bytes of `x` verbatim into `\v`, up to the `|`.
  - `\grab`'s body was tokenized with normal catcodes when `PRE` defined it. It restores the
    catcodes, runs `\v` with `\scantokens`, and ends the document.
  - `PRE` has no literal `|`: its delimiter is written as `^^7c`.
- **The code `x`** has three parts:
  - `\iffalse PRE \fi`, a copy of the prefix, which running the code skips;
  - the library, `library.inc`: the QR encoder and `\drawpanel`;
  - the template, `epilogue.inc`. It rebuilds the whole file from `\v` alone: characters 9 to
    8 + |PRE| (the copy of `PRE`), then `\v`, then `|`. It splits the file into thirds, runs the
    encoder on each, and adds the three matrices into one color matrix, which `\drawpanel`
    typesets.

**How the encoder works.** It is a direct expl3 port of the gnuplot QR encoder.
- `\intarray`s hold the matrix, the codewords and the Reed–Solomon generator.
- GF(256) products use log and antilog tables, and bitwise xor is a recursive macro, since expl3
  has none.
- It places the finder, timing and alignment patterns and the format (30660) and version (167017)
  information. It then encodes the data in byte mode, computes 25 Reed–Solomon blocks, interleaves
  them, and lays them out along the mask-0 serpentine.

**Golf.** `gen_encoder.py` golfs the expl3 code: it shortens names, gives long functions two-letter
aliases (`\cs_new_eq:NN`), and drops the spaces that expl3 ignores. The library goes from about
8 KB to about 5 KB. Without the golf, and with `PRE` rebuilt from character codes instead of the
`\iffalse` copy, the file needed four separate QR codes.

**Limits.** pdfTeX's main memory is fixed (5,000,000 words), and the page uses about 4.2 million of
them. That is why the cells avoid math mode and per-cell boxes. Compiling takes about three minutes.

## The development

- **The file model** is `lean/QuineEngine/TexScript.lean`.
  - **Files** have the shape `PRE ++ x ++ "|"`.
  - **The code.** The template's code is `"\iffalse" ++ PRE ++ "\fi" ++ lib ++ epi`. Run on data
    `d`, it outputs `slice d ++ d ++ "|"`, where `slice d` is `d`'s copy of the prefix.
  - **The quotation** is a second, octal-encoded code that outputs a fixed text.
  - **Admissible data.** The template's admissible data contain no `|`, are printable, and have
    `slice x = PRE`.
- **The barcode** is the abstract `Codec` of `lean/QuineEngine/Barcode.lean`. The three channels
  are hidden inside it, so its capacity is 8,859.
- **Kernel proofs.** The `decide +kernel` facts are split along the file's `++` structure, so that
  each piece is small enough for the kernel.
- **Result.** `quine_correct (Q : Codec) : 8859 ≤ Q.C → (system Q).IsQuine quine`. It depends
  only on `propext` and `Quot.sound`.

**What is trusted:**
1. pdfLaTeX runs files of the modelled shape as modelled;
2. `library.inc` and `epilogue.inc` implement a codec of capacity 8,859.

## Testing

Tested with Node.js 18.19.1 and npm 9.2.0, the npm packages jsqr 1.4.0, @zxing/library 0.21.3 and pngjs 7.0.0, which `npm install` installs at the versions pinned in `package-lock.json`, pdfTeX 1.40.25 from TeX Live 2023, and poppler's `pdftoppm` 24.02.0. From this folder:

```sh
npm install
node check.mjs
```

The check compiles each file with pdfLaTeX and renders the page twice:
- for jsQR, at 320 dpi with anti-aliasing, so the tinted symbols are present;
- for ZXing, crisply at about 4 pixels per module, thresholded at 50%.

It decodes each of the three channels with both decoders.
- **The encoder.** It draws the color code of random texts, up to the capacity, in a harness that
  uses the file's own pieces. Each text must decode correctly, and a text above the capacity must
  be rejected.
- **The quine.** The three channels of `qr-code.tex`'s page decode to the file itself.

A full run takes about twenty minutes.

To change the encoder, edit `encoder-source.tex`, run `python3 gen_encoder.py`, then rebuild with
`lake build`, run `lake exe quine`, and rerun the checks.
