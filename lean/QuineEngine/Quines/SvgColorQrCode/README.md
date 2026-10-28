# An SVG file that draws a color QR code of itself

An SVG file whose script draws an RGB-multiplexed QR code: three QR codes overlaid in the red,
green and blue channels, which together carry the file itself.

| File | Contents |
| --- | --- |
| `SvgColorQrCode.lean` | the instance of the engine and the proof |
| `drawcolor.js.inc` | the JavaScript library embedded in the file (a fragment, not a document) |
| `check.mjs` | tests the library and the file with real QR decoders |
| `color-qr.svg` | the quine, written by `lake exe quine` |

## The format

The text is split into thirds of lengths `⌈n/3⌉`, `⌈n/3⌉` and the rest. Each third is encoded as a
QR code: version 31 (141 × 141 modules), level L, byte mode, mask 0. In each module, the red channel
is dark where the first code is dark, the green channel where the second is, and the blue channel
where the third is. That gives eight colors; a module is white where all three codes are light.

To scan, separate the three channels, decode each as an ordinary QR code, and concatenate the
payloads. The capacity is 3 × 1,840 = 5,520 bytes.

This is a research convention, not a standardized barcode: ordinary scanners read only one
channel's worth, or nothing.

## The file

`color-qr.svg` is 2,045 bytes. It has the same shape as the SVG QR quine:

```
<svg xmlns='http://www.w3.org/2000/svg'><script>v="x";eval(v)</script></svg>
```

- **The code.** It is `ENC;drawColorQR(E)`, where `E` rebuilds the file from `v`.
- **The library.** `drawcolor.js.inc` is the QR encoder of `SvgQrCode/encoder.js`. Its matrix
  construction is factored into a function `C`, and a new `drawColorQR` draws one `<path>` per
  color.
- **Viewing.** It draws with a script, so open it directly in a browser; viewers that do not run
  scripts show it blank.

## The development

`SvgColorQrCode.lean` is a thin instance.

- The file model is `lean/QuineEngine/SvgScript.lean`, and the engine instance is
  `lean/QuineEngine/SvgCodec.lean`.
- The color code is the abstract `Codec` of `lean/QuineEngine/Barcode.lean`.
- The module supplies the library text and four facts about the concrete code, checked by
  `decide +kernel`.
- **Result.** `quine_correct (Q : Codec) : 5520 ≤ Q.C → (system Q).IsQuine quine`. It depends only
  on `propext` and `Quot.sound`.

**What is trusted:**
1. browsers run the modelled JavaScript fragment as modelled;
2. `drawcolor.js.inc` implements a codec of capacity 5,520;
3. XML passes the script text through unchanged.

## Testing

Tested with Node.js 18.19.1 and npm 9.2.0 and the npm packages jsqr 1.4.0, @zxing/library 0.21.3 and pngjs 7.0.0, which `npm install` installs at the versions pinned in `package-lock.json`. From this folder:

```sh
npm install
node check.mjs                  # fuzz the library, then check color-qr.svg
node check.mjs --png shot.png   # also decode a browser screenshot, channel by channel
```

The script runs the library with a stub `document`. It splits the drawing into its three channels,
decodes each with jsQR and ZXing, and checks that the concatenation is the original text:
- for random texts up to the 5,520-byte capacity, with a longer text rejected;
- for `color-qr.svg` itself, whose payload must be the file.
