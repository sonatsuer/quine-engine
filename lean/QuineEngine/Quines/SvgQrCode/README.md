# An SVG file that draws its own QR code

An SVG file which, when opened in a browser, draws a QR code whose payload is the file itself.

| File | Contents |
| --- | --- |
| `SvgQrCode.lean` | the model of the files, the instance of the engine, and the proof |
| `encoder.js` | the JavaScript QR encoder embedded in the file |
| `check.mjs` | tests the encoder and the file with real QR decoders |
| `qr-code.svg` | the quine, written by `lake exe quine` |

## Files and their meaning

The model of the files is in `lean/QuineEngine/SvgScript.lean`, shared with the SVG text quine.

A file has the shape

```
<svg xmlns='http://www.w3.org/2000/svg'><script>v="x";eval(arg)</script></svg>
```

It binds the string literal `x` to `v` and evaluates `arg`, which is either `v` or another string
literal. The evaluated code must have the form `ENC;drawQR(E)`.

- `ENC` is the JavaScript QR encoder in `encoder.js`, embedded with `include_str`.
- `E` is an expression (`Expr`) built from template literals, `v`, `H(n)` (that is,
  `String.fromCharCode(n)`) and `+`.
- `parseFile` and `parseCode` recognise this shape. `Disp` says that a file displays as the
  rendering of the value of `E`.
- Files of any other shape display nothing.
- String literals are read by `readLit`. They may contain printable characters and `\xHH` escapes.
- The script text must also pass `xmlRun`, an automaton that rejects `<`, `&` and `]]>`, so that an
  XML parser hands it to the browser unchanged.

## The QR code

The QR code is abstract. A `Codec`, defined in `lean/QuineEngine/Barcode.lean` and shared with
the PostScript quine, consists of:

- a capacity `C`;
- a type of grids;
- `encode` and `decode`;
- `decode_encode`, which says that decoding inverts encoding on texts of length at most `C`.

Representations are grids together with a formal representation for texts that are too long to
encode.

## The instance

- **Substitution.** `sub c x` binds `x` to `v` and evaluates the code `c`. When `c = x` it
  evaluates `v` itself, so the fixed point `sub a a` contains the code only once.
- **Quotation.** `quote t` stores `t` with `\xHH` escapes and evaluates `ENC;drawQR(v)`. Its
  domain is texts of Latin-1 characters that fit within the capacity.
- **Template.** The template `tmpl` is `ENC;drawQR(E)`. Here `tmplExpr` is the expression `E`,
  which builds the file `sub v v` from `v`, writing `<` and `"` as `H(60)` and `H(34)`. The lemma
  `eval_tmpl` states that it computes `sub x x` for every `x`.
- **Parsing lemmas.** `parseFile_sub` and `parseFile_quote` say that substituted and quoted files
  parse as intended. They rest on `readLit_raw`, `readLit_esc` and `xmlRun_esc`.

## Result

`quine_correct (Q : Codec) : 1840 ≤ Q.C → (system Q).IsQuine quine` is obtained from
`Diagonal.isQuine`.

- The facts about concrete texts are closed by `decide +kernel`: the template is safe and parses,
  and the quine has length 1,822, which is at most 1,840.
- The theorem depends only on `propext` and `Quot.sound`.

## What the model trusts

The theorem is about this model of SVG and JavaScript, and it holds for any codec. Applying it to
the real file assumes three things:

1. Browsers evaluate the modelled JavaScript fragment as modelled.
2. `encoder.js` implements a codec of capacity 1,840: QR version 31, error correction level L,
   byte mode, mask 0.
3. XML parsers pass the checked script text through unchanged.

`check.mjs` tests the encoder on random texts and checks the generated file with two independent
decoders, jsQR and ZXing. Given a screenshot from a real browser (`--png`), it decodes that as well.

## The encoder

The encoder is 1,617 bytes. It avoids `<`, `&`, `"` and `\`, so that it can sit unescaped inside
the string literal. `lakefile.toml` declares it as an `input_file` that the library `needs`, so
editing it rebuilds the module and re-checks the proofs.

## Testing

Tested with Node.js 18.19.1 and npm 9.2.0 and the npm packages jsqr 1.4.0, @zxing/library 0.21.3, pngjs 7.0.0 and @xmldom/xmldom 0.8.15, which `npm install` installs at the versions pinned in `package-lock.json`. From this folder:

```sh
npm install
node check.mjs                  # fuzz the encoder, then decode qr-code.svg with jsQR and ZXing
node check.mjs --png shot.png   # also decode a browser screenshot of qr-code.svg
```

Open `qr-code.svg` directly in a web browser (for example `firefox qr-code.svg`) to see the QR
code, and scan it with a phone. The file contains only a script that draws the code when it runs,
so viewers that do not run scripts show it blank: editor previews, image viewers, GitHub, and any
page that embeds the SVG as an image.
