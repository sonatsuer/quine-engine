# A PostScript file that prints an Aztec code of itself

A PostScript file which prints an Aztec code whose payload is the file itself.

| File | Contents |
| --- | --- |
| `PostScriptAztec.lean` | the instance of the engine and the proof |
| `encoder-source.ps.inc` | the readable PostScript Aztec encoder |
| `gen_encoder.py` | compresses the source into the loader `encoder.ps.inc` |
| `encoder.ps.inc` | the loader embedded in the file (a fragment, not a document) |
| `check.mjs` | renders with Ghostscript and tests with ZXing's Aztec reader |
| `aztec.ps` | the quine, written by `lake exe quine` |

## The format

The format is the same as the SVG Aztec quine's (see `../SvgAztec/README.md`): a full-range Aztec
symbol with 32 layers, 151 × 151 modules, with a guaranteed capacity of 2,278 bytes.

## The file

`aztec.ps` is 2,026 bytes and ends with a newline. It has the same shape as the PostScript QR
quine:

```
%!PS
(ENC <hex> exch cat <hex> cat Q showpage)dup cvx exec
```

**Compression.** The readable encoder `encoder-source.ps.inc` is 3,165 bytes, more than the Aztec
code can hold. So `ENC` is a loader:
- **Packing.** `gen_encoder.py` joins the source onto one line, compresses it with zlib, and writes
  it in Base64.
- **The loader.** It decodes the Base64 string, decompresses it with PostScript's `FlateDecode`
  filter, and executes the result, which defines `cat` and `Q`.
- **Size.** The loader is 1,936 bytes. Base64 contains no parentheses, backslashes or `%`, so it
  can sit unescaped in the string literal.
- **Model.** To the Lean model the loader is an opaque library text, like the other encoders.

`Q` draws the symbol with the `image` operator, one sample per module, 3 points per module. The
file opens in document viewers such as Evince and Xreader.

To change the encoder, edit `encoder-source.ps.inc`, run `python3 gen_encoder.py`, then rebuild
and rerun the checks.

## The development

`PostScriptAztec.lean` is a thin instance.

- The file model is `lean/QuineEngine/PsScript.lean`, and the engine instance is
  `lean/QuineEngine/PsCodec.lean`.
- The Aztec code is the abstract `Codec` of `lean/QuineEngine/Barcode.lean`.
- **Result.** `quine_correct (Q : Codec) : 2278 ≤ Q.C → (system Q).IsQuine quine`. It depends only
  on `propext` and `Quot.sound`.

**What is trusted:**
1. PostScript interpreters run the modelled fragment as modelled;
2. the loader, with the encoder it unpacks, implements a codec of capacity 2,278.

## Testing

Tested with Node.js 18.19.1 and npm 9.2.0, the npm packages @zxing/library 0.21.3 and pngjs 7.0.0, which `npm install` installs at the versions pinned in `package-lock.json`, and Ghostscript 10.02.1. From this folder:

```sh
npm install
node check.mjs
```

The script renders each file at 216 dpi and decodes the page with ZXing's Aztec reader:
- for random texts up to the capacity, with a 2,500-byte text rejected;
- for `aztec.ps` itself.

jsQR reads only QR codes, so ZXing is the only independent Aztec decoder used here.
