import QuineEngine.SvgCodec

/-!
# An SVG file that draws a color QR code of itself

The file has the shape of `QuineEngine.SvgScript`, and its evaluated code is `ENC;drawColorQR(E)`,
where `ENC` is the JavaScript library in `drawcolor.js.inc`. Displaying the file means drawing an
RGB-multiplexed QR code of the value of `E`: the text is split into thirds, each third is encoded as
a QR code (version 31, level L, byte mode, mask 0), and the three codes are overlaid in the red,
green and blue channels. Scanning separates the channels, decodes each, and concatenates.

The color code is the abstract `Codec` of `QuineEngine.Barcode`, and the engine instance is
`QuineEngine.SvgCodec`. The library is trusted to implement a codec of capacity 5520 (three times
1840); `check.mjs` tests this with two real decoders.
-/

namespace QuineEngine.SvgColorQrCode

open QuineEngine.Barcode QuineEngine.SvgScript

/-- The JavaScript library. It defines `H = String.fromCharCode` and `drawColorQR`. -/
def ENC : Text := (include_str "drawcolor.js.inc").toList

/-- The prefix of evaluated code: the library, then `;drawColorQR(`. -/
def cpre : Text := ENC ++ ";drawColorQR(".toList

theorem facts : SvgCodec.Facts cpre :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

abbrev system (Q : Codec) := SvgCodec.system cpre Q

/-- The engine's output: an SVG file that draws a color QR code of itself. -/
def quine : Text := SvgCodec.quineWith cpre

theorem quine_length : quine.length ≤ 5520 := by decide +kernel

theorem quine_all256 : quine.all (·.toNat < 256) = true := by decide +kernel

theorem quine_correct (Q : Codec) (hC : 5520 ≤ Q.C) : (system Q).IsQuine quine :=
  SvgCodec.quine_correct facts quine_length quine_all256 Q hC

end QuineEngine.SvgColorQrCode
