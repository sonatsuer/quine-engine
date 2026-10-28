import QuineEngine.PsCodec

/-!
# A PostScript file that prints a color QR code of itself

The file has the shape of `QuineEngine.PsScript`, and its library `ENC` is the PostScript code in
`encoder.ps.inc`, which defines `cat` and `Q`. `Q` prints an RGB-multiplexed QR code of its
argument: the text is split into thirds, each third is encoded as a QR code (version 31, level L,
byte mode, mask 0), and the three codes are overlaid in the red, green and blue channels.
Scanning separates the channels, decodes each, and concatenates.

The color code is the abstract `Codec` of `QuineEngine.Barcode`, and the engine instance is
`QuineEngine.PsCodec`. The library is trusted to implement a codec of capacity 5520 (three times
1840); `check.mjs` tests this with Ghostscript and two real decoders.
-/

namespace QuineEngine.PostScriptColorQrCode

open QuineEngine.Barcode QuineEngine.PsScript

/-- The PostScript library. It defines `cat` and `Q`. -/
def ENC : Text := (include_str "encoder.ps.inc").toList

theorem facts : PsCodec.Facts ENC :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

abbrev system (Q : Codec) := PsCodec.system ENC Q

/-- The engine's output: a PostScript file that prints a color QR code of itself. -/
def quine : Text := PsCodec.quineWith ENC

theorem quine_length : quine.length ≤ 5520 := by decide +kernel

theorem quine_all256 : quine.all (·.toNat < 256) = true := by decide +kernel

theorem quine_correct (Q : Codec) (hC : 5520 ≤ Q.C) : (system Q).IsQuine quine :=
  PsCodec.quine_correct facts quine_length quine_all256 Q hC

end QuineEngine.PostScriptColorQrCode
