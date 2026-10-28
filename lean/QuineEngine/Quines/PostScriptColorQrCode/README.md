# A PostScript file that prints a color QR code of itself

A PostScript file which prints an RGB-multiplexed QR code: three QR codes overlaid in the red,
green and blue channels, which together carry the file itself.

| File | Contents |
| --- | --- |
| `PostScriptColorQrCode.lean` | the instance of the engine and the proof |
| `encoder.ps.inc` | the PostScript library embedded in the file (a fragment, not a document) |
| `check.mjs` | renders with Ghostscript and tests with real QR decoders |
| `color-qr.ps` | the quine, written by `lake exe quine` |

## The format

The format is the same as the SVG color quine's (see `../SvgColorQrCode/README.md`):
- the text is split into thirds;
- each third becomes a QR code, version 31, level L, byte mode, mask 0;
- the three codes are overlaid in the red, green and blue channels;
- scanning separates the channels, decodes each, and concatenates.

The capacity is 5,520 bytes.

## The file

`color-qr.ps` is 3,192 bytes and ends with a newline. It has the same shape as the PostScript QR
quine:

```
%!PS
(ENC <hex> exch cat <hex> cat Q showpage)dup cvx exec
```

The library `encoder.ps.inc` starts from the PostScript QR encoder of `PostScriptQrCode`, switched
to version 31.
- **Matrix.** The matrix construction becomes a procedure `MM`.
- **`Q`.** It splits its argument into thirds, builds the three matrices, and draws them as one
  RGB image (`colorimage`), with one sample per module. As in the QR quine, an image is sampled at
  pixel centres, so modules do not grow.
- **Size.** Each module is 3 points, so the symbol fits on A4 and Letter paper.
- **Viewing.** The file opens in document viewers such as Evince and Xreader.

## The development

`PostScriptColorQrCode.lean` is a thin instance.

- The file model is `lean/QuineEngine/PsScript.lean`, and the engine instance is
  `lean/QuineEngine/PsCodec.lean`.
- The color code is the abstract `Codec` of `lean/QuineEngine/Barcode.lean`.
- The module supplies the library text and four facts about the concrete code, checked by
  `decide +kernel`.
- **Result.** `quine_correct (Q : Codec) : 5520 ≤ Q.C → (system Q).IsQuine quine`. It depends only
  on `propext` and `Quot.sound`.

**What is trusted:**
1. PostScript interpreters run the modelled fragment as modelled;
2. `encoder.ps.inc` implements a codec of capacity 5,520.

## Testing

Tested with Node.js 18.19.1 and npm 9.2.0, the npm packages jsqr 1.4.0, @zxing/library 0.21.3 and pngjs 7.0.0, which `npm install` installs at the versions pinned in `package-lock.json`, and Ghostscript 10.02.1. From this folder:

```sh
npm install
node check.mjs
```

The script renders each file in color at 216 dpi, where a module is exactly 9 pixels, and splits
the page into its three channels. jsQR reads each whole channel, and ZXing reads each channel
cropped to the symbol, in pure-barcode mode. The script checks that the concatenated payloads are
the original text:
- for random texts up to the capacity, with a longer text rejected;
- for `color-qr.ps` itself.
