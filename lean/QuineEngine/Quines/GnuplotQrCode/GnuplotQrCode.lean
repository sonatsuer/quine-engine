import QuineEngine.Barcode
import QuineEngine.GpScript

/-!
# A gnuplot script that plots a QR code of itself

The file has the shape of `QuineEngine.GpScript`, and its library `ENC` is `encoder.gp.inc`, a
QR encoder written in gnuplot that plots the QR code of the string `s` (version 40, level L, byte
mode, mask 0). It is generated from the readable `encoder-source.gp` by `gen_encoder.py`.

The QR code is the abstract `Codec` of `QuineEngine.Barcode`. The library is trusted to implement
a codec of capacity 2953, the byte capacity of version 40-L; `check.mjs` tests this with gnuplot,
jsQR and ZXing.
-/

namespace QuineEngine.GnuplotQrCode

open QuineEngine.Barcode QuineEngine.GpScript

/-- The gnuplot library: a QR encoder that plots the string `s`. -/
def ENC : Text := (include_str "encoder.gp.inc").toList

/-- A file plots the QR code of the string that `s` receives, when it has the expected shape. -/
def Disp (Q : Codec) (f : Text) (p : Q.Grid ⊕ Text) : Prop :=
  ∃ x c e, parseFile f = some (x, c) ∧ parseCodeWith ENC c = some e ∧
    (e.eval x).length ≤ Q.C ∧ (e.eval x).all printable = true ∧ p = render Q (e.eval x)

def system (Q : Codec) : System Text (Q.Grid ⊕ Text) where
  disp := Disp Q
  scan := scan Q
  render := render Q
  scan_render := scan_render Q

theorem safe_show : safe (showWith ENC) = true := by decide +kernel
theorem parse_show : parseCodeWith ENC (showWith ENC) = some .var := by decide +kernel
theorem safe_tmpl : safe (tmplWith ENC) = true := by decide +kernel
theorem parse_tmpl : parseCodeWith ENC (tmplWith ENC) = some tmplExpr := by decide +kernel

def quotation (Q : Codec) : Quotation (system Q) where
  Dom t := t.all printable = true ∧ t.length ≤ Q.C
  q := quoteWith ENC
  disp_q t ht := ⟨render Q t, ⟨t, showWith ENC, .var, parseFile_quoteWith ENC safe_show t ht.1,
    parse_show, ht.2, ht.1, rfl⟩, rfl⟩

def diagonal (Q : Codec) : Diagonal (system Q) (quotation Q) where
  sub := sub
  a := tmplWith ENC
  Ok x := safe x = true
  spec := by
    intro x hx s ⟨p, hd, hs⟩
    obtain ⟨x', c', e, hf, hc, hlen, hpr, hp⟩ := hd
    change parseFile (quoteWith ENC (sub x x)) = _ at hf
    rw [parseFile_quoteWith ENC safe_show _ (printable_sub hx)] at hf
    cases hf
    rw [parse_show] at hc
    cases hc
    subst hp
    change scan Q (render Q (sub x x)) = _ at hs
    rw [scan_render] at hs
    cases hs
    refine ⟨render Q (sub x x), ⟨x, tmplWith ENC, tmplExpr, parseFile_sub safe_tmpl hx,
      parse_tmpl, ?_, ?_, ?_⟩, scan_render Q _⟩
    · rw [eval_tmpl]
      exact hlen
    · rw [eval_tmpl]
      exact hpr
    · rw [eval_tmpl]

/-- The engine's output: a gnuplot script that plots a QR code of itself. -/
def quine : Text := sub (tmplWith ENC) (tmplWith ENC)

theorem quine_length : quine.length ≤ 2953 := by decide +kernel

theorem quine_printable : quine.all printable = true := by decide +kernel

theorem quine_correct (Q : Codec) (hC : 2953 ≤ Q.C) : (system Q).IsQuine quine :=
  (diagonal Q).isQuine safe_tmpl ⟨quine_printable, Nat.le_trans quine_length hC⟩

end QuineEngine.GnuplotQrCode
