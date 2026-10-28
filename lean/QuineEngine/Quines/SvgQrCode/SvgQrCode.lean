import QuineEngine.SvgCodec

/-!
# An SVG file that draws a QR code of itself

Texts are SVG files of a fixed shape. The file
```
<svg xmlns='http://www.w3.org/2000/svg'><script>v="x";eval(arg)</script></svg>
```
binds the string literal `x` to `v` and evaluates `arg`, which is either `v` itself or a string
literal. The evaluated code is `ENC;drawQR(E)`, where `ENC` is the JavaScript QR encoder in
`encoder.js` (in this folder) and `E` is an expression built from string literals, `v`, `H(n)`
(that is, `String.fromCharCode(n)`) and `+`. Displaying the file means drawing the QR code of the
value of `E`.

The QR code itself is abstract: the `Codec` of `QuineEngine.Barcode`, a capacity and a decoder that
inverts the encoder. The JavaScript encoder is trusted to implement such a codec for capacity 1840
(version 31, level L, byte mode); `check.mjs` tests this with two real decoders.

The model of the files is `QuineEngine.SvgScript` and the engine instance is `QuineEngine.SvgCodec`.
The semantics is deliberately conservative: files that do not parse display nothing. It is faithful
for the files it accepts, because their script text contains no `<` or `&` and no `]]>` (so the XML
parser passes it through unchanged) and their string literals use only printable characters and
`\xHH` escapes.
-/

namespace QuineEngine.SvgQrCode

open QuineEngine.Barcode QuineEngine.SvgScript

/-- The JavaScript QR encoder. It defines `H = String.fromCharCode` and `drawQR`. -/
def ENC : Text := (include_str "encoder.js").toList

/-- The prefix of evaluated code: the encoder, then `;drawQR(`. -/
def cpre : Text := ENC ++ ";drawQR(".toList

theorem facts : SvgCodec.Facts cpre :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

abbrev system (Q : Codec) := SvgCodec.system cpre Q

/-- The quotation: a file that draws the QR code of a given text. -/
def quote (t : Text) : Text := quoteWith cpre t

/-- The template `ENC;drawQR(E)`. -/
def tmpl : Text := SvgCodec.tmplWith cpre

/-- The engine's output: an SVG file that draws a QR code of itself. -/
def quine : Text := SvgCodec.quineWith cpre

theorem quine_length : quine.length ≤ 1840 := by decide +kernel

theorem quine_all256 : quine.all (·.toNat < 256) = true := by decide +kernel

theorem quine_correct (Q : Codec) (hC : 1840 ≤ Q.C) : (system Q).IsQuine quine :=
  SvgCodec.quine_correct facts quine_length quine_all256 Q hC

end QuineEngine.SvgQrCode
