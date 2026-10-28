# An SVG file that draws an Aztec code of itself

An SVG file whose script draws an Aztec code whose payload is the file itself.

| File | Contents |
| --- | --- |
| `SvgAztec.lean` | the instance of the engine and the proof |
| `drawaztec.js.inc` | the JavaScript Aztec encoder embedded in the file (a fragment, not a document) |
| `check.mjs` | tests the encoder and the file with ZXing's Aztec reader |
| `aztec.svg` | the quine, written by `lake exe quine` |

## The format

Aztec is a 2D barcode standardized as ISO/IEC 24778. It has a bullseye in the centre and no need
for a quiet zone. The encoder writes a full-range symbol with a fixed 32 layers, 151 × 151 modules:

- **Data.** The text is written from Upper mode in binary-shift segments of at most 2,078 bytes.
  Each segment has a 5-bit length, or 5 zero bits followed by an 11-bit length.
- **Bit stuffing.** The bits are cut into 12-bit codewords. A codeword whose first 11 bits are
  all equal gets a complementary last bit, and the bit it displaced starts the next codeword.
- **Error correction.** Reed–Solomon over GF(4096) uses every codeword the text leaves free; at
  least 3 are required.
- **Mode message.** Layers − 1 and data codewords − 1, protected by Reed–Solomon over GF(16),
  sit around the bullseye. The reference grid and the spiral layout of the layers follow the
  standard.
- **The empty text** becomes one padding codeword.

The guaranteed capacity is 2,278 bytes. That is the most that fits in 32 layers with 3
error-correction codewords even if every codeword is stuffed; longer texts may or may not fit.

The structure follows ZXing's `AztecEncoder` (Apache-2.0), reimplemented from the specification.

## The file

`aztec.svg` is 2,072 bytes. It has the same shape as the SVG QR quine,
`<svg …><script>v="x";eval(v)</script></svg>`, with the code `ENC;drawAztec(E)`.

- **The encoder.** `drawaztec.js.inc` is 1,864 bytes. It avoids `<`, `&`, `"` and `\`, so shifts
  become divisions by powers of two and masks become `%`.
- **Viewing.** It draws with a script, so open it directly in a browser.

## The development

`SvgAztec.lean` is a thin instance.

- The file model is `lean/QuineEngine/SvgScript.lean`, and the engine instance is
  `lean/QuineEngine/SvgCodec.lean`.
- The Aztec code is the abstract `Codec` of `lean/QuineEngine/Barcode.lean`.
- **Result.** `quine_correct (Q : Codec) : 2278 ≤ Q.C → (system Q).IsQuine quine`. It depends only
  on `propext` and `Quot.sound`.

**What is trusted:**
1. browsers run the modelled JavaScript fragment as modelled;
2. `drawaztec.js.inc` implements a codec of capacity 2,278;
3. XML passes the script text through unchanged.

## Testing

Tested with Node.js 18.19.1 and npm 9.2.0 and the npm packages @zxing/library 0.21.3 and pngjs 7.0.0, which `npm install` installs at the versions pinned in `package-lock.json`. From this folder:

```sh
npm install
node check.mjs                  # fuzz the encoder, then check aztec.svg
node check.mjs --png shot.png   # also decode a browser screenshot
```

The script runs the encoder with a stub `document`, rasterises the drawing, and decodes it with
ZXing's Aztec reader:
- for random texts up to the capacity, including both sides of the segment boundary at 2,078
  bytes, with a 2,500-byte text rejected;
- for `aztec.svg` itself.

jsQR reads only QR codes, so ZXing is the only independent Aztec decoder used here.
