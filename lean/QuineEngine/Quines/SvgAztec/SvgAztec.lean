import QuineEngine.SvgCodec

/-!
# An SVG file that draws an Aztec code of itself

The file has the shape of `QuineEngine.SvgScript`, and its evaluated code is `ENC;drawAztec(E)`,
where `ENC` is the JavaScript Aztec encoder in `drawaztec.js.inc`. Displaying the file means
drawing a full-range Aztec code (32 layers, 151 × 151 modules) of the value of `E`.

The Aztec code is the abstract `Codec` of `QuineEngine.Barcode`, and the engine instance is
`QuineEngine.SvgCodec`. The encoder is trusted to implement a codec of capacity 2278, the most
bytes that fit in 32 layers with at least 3 error-correction codewords whatever the bit stuffing;
`check.mjs` tests this with ZXing's Aztec reader.
-/

namespace QuineEngine.SvgAztec

open QuineEngine.Barcode QuineEngine.SvgScript

/-- The JavaScript Aztec encoder. It defines `H = String.fromCharCode` and `drawAztec`. -/
def ENC : Text := (include_str "drawaztec.js.inc").toList

/-- The prefix of evaluated code: the encoder, then `;drawAztec(`. -/
def cpre : Text := ENC ++ ";drawAztec(".toList

theorem facts : SvgCodec.Facts cpre :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

abbrev system (Q : Codec) := SvgCodec.system cpre Q

/-- The engine's output: an SVG file that draws an Aztec code of itself. -/
def quine : Text := SvgCodec.quineWith cpre

theorem quine_length : quine.length ≤ 2278 := by decide +kernel

theorem quine_all256 : quine.all (·.toNat < 256) = true := by decide +kernel

theorem quine_correct (Q : Codec) (hC : 2278 ≤ Q.C) : (system Q).IsQuine quine :=
  SvgCodec.quine_correct facts quine_length quine_all256 Q hC

end QuineEngine.SvgAztec
