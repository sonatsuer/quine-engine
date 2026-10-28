import QuineEngine.PsCodec

/-!
# A PostScript file that prints a QR code of itself

Texts are PostScript files of a fixed shape:
```
%!PS
(x)dup cvx exec          or          (x)(c)cvx exec          or          <hex>(c)cvx exec
```
The file pushes the string `x` and executes the code `x` (first form) or `c` (other forms) with
that string on the stack. String literals are `(…)` with balanced parentheses and no backslash, or
`<…>` in hexadecimal. The executed code must be `ENC` followed by a tail of `<hex>`, `exch` and
`cat`, ending in `Q showpage`. Here `ENC` is the PostScript QR encoder in `encoder.ps.inc`, which
defines `cat` (concatenate two strings) and `Q` (draw the QR code of the string on the stack).
Displaying the file means printing the page with the QR code of the string that `Q` receives. Files
end with a newline, which document viewers based on libspectre require.

The model of the files is `QuineEngine.PsScript` and the engine instance is `QuineEngine.PsCodec`.
The QR code is the abstract codec of `QuineEngine.Barcode`. The encoder is trusted to implement it
for capacity 2953 (version 40, level L, byte mode, mask 0); `check.mjs` tests this with Ghostscript
and two real decoders. The semantics is conservative: files of any other shape display nothing.
-/

namespace QuineEngine.PostScriptQrCode

open QuineEngine.Barcode QuineEngine.PsScript

/-- The PostScript QR encoder. It defines `cat` and `Q`. -/
def ENC : Text := (include_str "encoder.ps.inc").toList

theorem facts : PsCodec.Facts ENC :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

abbrev system (Q : Codec) := PsCodec.system ENC Q

/-- The quotation: a file that prints the QR code of a given text. -/
def quote (t : Text) : Text := quoteWith ENC t

/-- The template: `ENC` and a tail that rebuilds the file around the string on the stack. -/
def tmpl : Text := tmplWith ENC

/-- The engine's output: a PostScript file that prints a QR code of itself. -/
def quine : Text := PsCodec.quineWith ENC

theorem quine_length : quine.length ≤ 2953 := by decide +kernel

theorem quine_all256 : quine.all (·.toNat < 256) = true := by decide +kernel

theorem quine_correct (Q : Codec) (hC : 2953 ≤ Q.C) : (system Q).IsQuine quine :=
  PsCodec.quine_correct facts quine_length quine_all256 Q hC

end QuineEngine.PostScriptQrCode
