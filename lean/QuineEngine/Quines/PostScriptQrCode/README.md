# A PostScript file that prints a QR code of itself

A PostScript file which, when printed or viewed, shows a QR code whose payload is the file itself.

| File | Contents |
| --- | --- |
| `PostScriptQrCode.lean` | the model of the files, the instance of the engine, and the proof |
| `encoder.ps.inc` | the PostScript QR encoder embedded in the file (a fragment, not a document) |
| `check.mjs` | renders with Ghostscript and tests with real QR decoders |
| `qr-code.ps` | the quine, written by `lake exe quine` |

## The file

`qr-code.ps` is 2,820 bytes and has the shape

```
%!PS
(ENC <hex> exch cat <hex> cat Q showpage)dup cvx exec
```

The second line pushes the string between the parentheses, duplicates it, and executes the copy.
So the code runs with its own text on the stack.

The file ends with a newline, which is part of what it reproduces. Document viewers built on
libspectre, such as Xreader and Evince, refuse PostScript files that do not end with one.

- `ENC` is the QR encoder in `encoder.ps.inc`. It defines `cat`, which concatenates two strings, and
  `Q`, which draws the QR code of the string on the stack.
- The two hex strings are `%!PS` plus newline plus `(`, and `)dup cvx exec` plus newline. Around
  the string on the stack they rebuild the whole file, which `Q` then draws.
- Hex strings contain no parentheses and no backslashes, so the code can sit unescaped inside the
  `(…)` literal.

The QR code is version 40 (177 × 177 modules), error correction level L, byte mode, with the mask
fixed to 0. Its capacity is 2,953 bytes. Each module is 3 points, so the symbol fits on both A4
and Letter paper.

## The development

**Files and their meaning.** `parseFile` accepts three shapes:

```
%!PS
(x)dup cvx exec          (x)(c)cvx exec          <hex>(c)cvx exec
```

- Each one pushes a string and executes the code `x` or `c`. Literals are read by `readRaw` (a
  balanced `(…)` with no backslash) and `readHex` (a `<…>` in lowercase hexadecimal).
- The executed code must be `ENC` followed by a tail of `<hex>`, `exch` and `cat`, ending in
  `Q showpage`. `parseCode` recognises it and `runOps` runs it.
- The file displays as the QR code of the string that `Q` receives. Files of any other shape
  display nothing.

**The QR code** is the abstract `Codec` of `lean/QuineEngine/Barcode.lean`, shared with the SVG
quine.

**The instance.**

- **Substitution.** `sub c x` pushes `x` and executes `c`. When `c = x` it executes `dup cvx exec`
  instead, so the fixed point contains the code only once.
- **Quotation.** `quote t` pushes `t` as a hex string and executes `ENC Q showpage`. Its domain is
  texts of Latin-1 characters that fit within the capacity.
- **Template.** `tmpl` is the code shown above. `parseCode_tmpl` and `runOps_tmpl` show that it
  builds `sub x x` from `x`.
- **Parsing lemmas.** `parseFile_sub` and `parseFile_quote` rest on `readRaw_balanced` and
  `readHex_hexOf`.
- **Side condition.** `Ok x` is `safe x`: printable ASCII, no backslash, balanced parentheses.

**Result.** `quine_correct (Q : Codec) : 2953 ≤ Q.C → (system Q).IsQuine quine` is obtained from
`Diagonal.isQuine`.

- The facts about concrete texts are closed by `decide +kernel`: the template is safe and parses,
  and the quine is Latin-1 with length at most 2,953.
- The theorem depends only on `propext` and `Quot.sound`.

## What the model trusts

The theorem is about this model of PostScript, and it holds for any codec. Applying it to the
real file assumes three things:

1. PostScript interpreters run the modelled fragment as modelled: string literals, `dup`, `cvx`,
   `exec`, and the tail operators.
2. `encoder.ps.inc` implements a codec of capacity 2,953: QR version 40, level L, byte mode, mask 0.
3. `cat` concatenates and `Q` draws the QR code of its argument.

`check.mjs` tests the encoder on random texts and checks the generated file.

## The encoder

The encoder is 2,730 bytes, on one line. It contains no `\`, no `%` and no parentheses, so it can
sit inside a `(…)` literal and still be executed as code. It draws the symbol with the `image`
operator rather than with filled rectangles. PostScript fills every pixel a shape touches, which
would make dark modules grow and confuse decoders.

`lakefile.toml` declares `encoder.ps.inc` as an `input_file` that the library `needs`, so editing it
rebuilds the module and re-checks the proofs.

## Testing

Tested with Node.js 18.19.1 and npm 9.2.0, the npm packages jsqr 1.4.0, @zxing/library 0.21.3 and pngjs 7.0.0, which `npm install` installs at the versions pinned in `package-lock.json`, and Ghostscript 10.02.1. From this folder:

```sh
npm install
node check.mjs
```

The script renders each file with Ghostscript at 216 dpi, where a module is exactly 9 pixels.
- **Fuzz test.** It runs the encoder on random texts of up to 2,953 bytes, decodes each page with
  both decoders, and checks that a longer text is rejected.
- **The quine.** It renders `qr-code.ps` and checks that both decoders read back exactly the
  file's bytes. jsQR reads the whole page; ZXing reads the symbol, cropped to its quiet zone, in
  pure-barcode mode.

To see the page, run `gs qr-code.ps`, or convert it with `ps2pdf qr-code.ps` and open the PDF.
