import QuineEngine.PsCodec

/-!
# A PostScript file that prints an Aztec code of itself

The file has the shape of `QuineEngine.PsScript`, and its library `ENC` is `encoder.ps.inc`, which
defines `cat` and `Q`; `Q` prints a full-range Aztec code (32 layers, 151 × 151 modules) of its
argument. The library is a loader: it decodes a Base64 string, decompresses it with PostScript's
FlateDecode filter, and executes the result (the readable encoder in `encoder-source.ps.inc`). To
the model it is an opaque text like any other library.

The Aztec code is the abstract `Codec` of `QuineEngine.Barcode`, and the engine instance is
`QuineEngine.PsCodec`. The library is trusted to implement a codec of capacity 2278, the most bytes
that fit in 32 layers with at least 3 error-correction codewords whatever the bit stuffing;
`check.mjs` tests this with Ghostscript and ZXing's Aztec reader.
-/

namespace QuineEngine.PostScriptAztec

open QuineEngine.Barcode QuineEngine.PsScript

/-- The PostScript library: a loader for the compressed Aztec encoder. It defines `cat` and `Q`. -/
def ENC : Text := (include_str "encoder.ps.inc").toList

theorem facts : PsCodec.Facts ENC :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

abbrev system (Q : Codec) := PsCodec.system ENC Q

/-- The engine's output: a PostScript file that prints an Aztec code of itself. -/
def quine : Text := PsCodec.quineWith ENC

theorem quine_length : quine.length ≤ 2278 := by decide +kernel

theorem quine_all256 : quine.all (·.toNat < 256) = true := by decide +kernel

theorem quine_correct (Q : Codec) (hC : 2278 ≤ Q.C) : (system Q).IsQuine quine :=
  PsCodec.quine_correct facts quine_length quine_all256 Q hC

end QuineEngine.PostScriptAztec
