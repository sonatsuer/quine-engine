import QuineEngine.Barcode
import QuineEngine.PyScript

/-!
# A Python program whose sound has a spectrogram that is a QR code of itself

The program makes a sound whose spectrogram shows the QR code of its own source (version 40,
level L, byte mode, mask 0). Time is the horizontal axis: each module column is 0.2 s. Frequency
is the vertical axis: each module row is a pair of tones 10 Hz apart, and the rows are 50 Hz apart.
A light module sounds, and a dark one is silent. The program plays the sound with `miniaudio`, or
with the flag `-w` writes it to stdout as a WAV file.

The file has the shape of `QuineEngine.PyScript`, and its library `ENC` is `spectrogram.py.inc`,
which defines `qr`, a QR encoder in pure Python, and `play`. The QR code is the abstract `Codec`
of `QuineEngine.Barcode`. The library is trusted to make a sound whose spectrogram is the QR code
of a codec of capacity 2953, the byte capacity of version 40-L; `check.py` draws the
spectrograms and decodes them with zxing-cpp.
-/

namespace QuineEngine.PythonSpectrogram

open QuineEngine.Barcode QuineEngine.PyScript

/-- The library: everything before the call `play(…)`. -/
def ENC : Text := (include_str "spectrogram.py.inc").toList

def PRE : Text := ENC ++ "play(".toList

/-- A file sounds the QR code of the string that `play` receives. -/
def Disp (Q : Codec) (f : Text) (p : Q.Grid ⊕ Text) : Prop :=
  ∃ x c e, parseFile f = some (x, c) ∧ parseCodeWith PRE c = some e ∧
    (e.eval x).length ≤ Q.C ∧ (e.eval x).all (·.toNat < 128) = true ∧ p = render Q (e.eval x)

def system (Q : Codec) : System Text (Q.Grid ⊕ Text) where
  disp := Disp Q
  scan := scan Q
  render := render Q
  scan_render := scan_render Q

theorem safe_show : safe (showWith PRE) = true := by decide +kernel
theorem parse_show : parseCodeWith PRE (showWith PRE) = some .var := by decide +kernel
theorem safe_tmpl : safe (tmplWith PRE) = true := by decide +kernel
theorem parse_tmpl : parseCodeWith PRE (tmplWith PRE) = some tmplExpr := by decide +kernel

def quotation (Q : Codec) : Quotation (system Q) where
  Dom t := t.all (·.toNat < 128) = true ∧ t.length ≤ Q.C
  q := quoteWith PRE
  disp_q t ht := ⟨render Q t, ⟨t, showWith PRE, .var, parseFile_quoteWith PRE safe_show t ht.1,
    parse_show, ht.2, ht.1, rfl⟩, rfl⟩

def diagonal (Q : Codec) : Diagonal (system Q) (quotation Q) where
  sub := sub
  a := tmplWith PRE
  Ok x := safe x = true
  spec := by
    intro x hx s ⟨p, hd, hs⟩
    obtain ⟨x', c', e, hf, hc, hlen, hok, hp⟩ := hd
    change parseFile (quoteWith PRE (sub x x)) = _ at hf
    rw [parseFile_quoteWith PRE safe_show _ (all128_sub hx)] at hf
    cases hf
    rw [parse_show] at hc
    cases hc
    subst hp
    change scan Q (render Q (sub x x)) = _ at hs
    rw [scan_render] at hs
    cases hs
    refine ⟨render Q (sub x x), ⟨x, tmplWith PRE, tmplExpr, parseFile_sub safe_tmpl hx,
      parse_tmpl, ?_, ?_, ?_⟩, scan_render Q _⟩
    · rw [eval_tmpl]
      exact hlen
    · rw [eval_tmpl]
      exact hok
    · rw [eval_tmpl]

/-- The engine's output: a Python program whose sound has a spectrogram that is a QR code of
itself. -/
def quine : Text := sub (tmplWith PRE) (tmplWith PRE)

theorem quine_length : quine.length ≤ 2953 := by decide +kernel

theorem quine_ok : quine.all (·.toNat < 128) = true := by decide +kernel

/-- **The spectrogram quine.** -/
theorem quine_correct (Q : Codec) (hC : 2953 ≤ Q.C) : (system Q).IsQuine quine :=
  (diagonal Q).isQuine safe_tmpl ⟨quine_ok, Nat.le_trans quine_length hC⟩

end QuineEngine.PythonSpectrogram
