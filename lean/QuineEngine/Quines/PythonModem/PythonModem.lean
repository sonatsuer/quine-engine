import QuineEngine.PyScript
import QuineEngine.Uart

/-!
# A Python program that plays itself as a modem

The program plays its own source as a 300-baud Bell 103 modem, with `miniaudio`. Each byte is an
8N1 frame (a start bit 0, eight data bits least significant first, a stop bit 1), and each bit is
a tone, 1270 Hz for a mark (1) and 1070 Hz for a space (0).

The file has the shape of `QuineEngine.PyScript`, and its library `ENC` is `modem.py.inc`, which
defines `play`. The framing is the concrete one of `QuineEngine.Uart`: `cell` maps a character to
its frame and `uncell` reads it back, so the theorem has no hypotheses. The library is trusted to play the frames of its argument
as tones; `check.py` captures the samples and demodulates them.
-/

namespace QuineEngine.PythonModem

open QuineEngine.PyScript

/-! ## The representation system: UART frames (`QuineEngine.Uart`) -/

open QuineEngine.Uart (ok render scan scan_render)

/-- The library: everything before the call `play(…)`. -/
def ENC : Text := (include_str "modem.py.inc").toList

def PRE : Text := ENC ++ "play(".toList

/-- A file plays the frames of the string that `play` receives. -/
def Disp (f : Text) (p : List (List Bool) ⊕ Text) : Prop :=
  ∃ x c e, parseFile f = some (x, c) ∧ parseCodeWith PRE c = some e ∧
    (e.eval x).all ok = true ∧ p = render (e.eval x)

def system : System Text (List (List Bool) ⊕ Text) where
  disp := Disp
  scan := scan
  render := render
  scan_render := scan_render

/-! ## The quine -/

theorem safe_show : safe (showWith PRE) = true := by decide +kernel
theorem parse_show : parseCodeWith PRE (showWith PRE) = some .var := by decide +kernel
theorem safe_tmpl : safe (tmplWith PRE) = true := by decide +kernel
theorem parse_tmpl : parseCodeWith PRE (tmplWith PRE) = some tmplExpr := by decide +kernel

def quotation : Quotation system where
  Dom t := t.all ok = true
  q := quoteWith PRE
  disp_q t ht := ⟨render t, ⟨t, showWith PRE, .var, parseFile_quoteWith PRE safe_show t ht,
    parse_show, ht, rfl⟩, rfl⟩

def diagonal : Diagonal system quotation where
  sub := sub
  a := tmplWith PRE
  Ok x := safe x = true
  spec := by
    intro x hx s ⟨p, hd, hs⟩
    obtain ⟨x', c', e, hf, hc, hok, hp⟩ := hd
    change parseFile (quoteWith PRE (sub x x)) = _ at hf
    rw [parseFile_quoteWith PRE safe_show _ (all128_sub hx)] at hf
    cases hf
    rw [parse_show] at hc
    cases hc
    subst hp
    change scan (render (sub x x)) = _ at hs
    rw [scan_render] at hs
    cases hs
    refine ⟨render (sub x x), ⟨x, tmplWith PRE, tmplExpr, parseFile_sub safe_tmpl hx, parse_tmpl,
      ?_, ?_⟩, scan_render _⟩
    · rw [eval_tmpl]
      exact hok
    · rw [eval_tmpl]

/-- The engine's output: a Python program that plays itself as a modem. -/
def quine : Text := diagonal.quine

theorem quine_ok : quine.all ok = true := by decide +kernel

/-- **The modem quine.** -/
theorem quine_correct : system.IsQuine quine := diagonal.isQuine safe_tmpl quine_ok

end QuineEngine.PythonModem
