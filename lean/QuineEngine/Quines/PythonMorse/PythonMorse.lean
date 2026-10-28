import QuineEngine.PyScript

/-!
# A Python program that blinks itself in Morse code

The program opens a window and blinks its own source in International Morse code, white for
light and black for dark. Morse code has no case and few symbols, so the program is written in the
57 characters that have codes: lower-case letters, digits, `. , ? ! / ( ) & : ; = + - _ $ @ " '`,
a line break (the prosign AA) and the space (a longer gap).

The file has the shape of `QuineEngine.PyScript`, and its library `ENC` is `morse.py.inc`, which
defines `blink`. The Morse code is concrete: `cell` maps a character to its code and `uncell`
reads it back, so the theorem has no hypotheses. The library is trusted to blink the codes of its
argument; `check.py` records the light and decodes it by timing.
-/

namespace QuineEngine.PythonMorse

open QuineEngine.PyScript

/-! ## Morse code -/

/-- The characters with a code. -/
def KEYS : Text := "abcdefghijklmnopqrstuvwxyz0123456789.,?!/()&:;=+-_$@\"'\n ".toList

/-- Their codes: International Morse (ITU-R M.1677-1) with `!`, `$` and `_`, the prosign AA for
a line break, and the empty code for a space. -/
def CODES : List Text := [".-", "-...", "-.-.", "-..", ".", "..-.", "--.", "....", "..", ".---",
  "-.-", ".-..", "--", "-.", "---", ".--.", "--.-", ".-.", "...", "-", "..-", "...-", ".--",
  "-..-", "-.--", "--..", "-----", ".----", "..---", "...--", "....-", ".....", "-....", "--...",
  "---..", "----.", ".-.-.-", "--..--", "..--..", "-.-.--", "-..-.", "-.--.", "-.--.-", ".-...",
  "---...", "-.-.-.", "-...-", ".-.-.", "-....-", "..--.-", "...-..-", ".--.-.", ".-..-.",
  ".----.", ".-.-", ""].map String.toList

def TABLE : List (Char × Text) := KEYS.zip CODES

def ok (c : Char) : Bool := decide (c ∈ KEYS)

/-- The Morse code of a character. -/
def cell (c : Char) : Text := ((TABLE.find? (·.1 = c)).map (·.2)).getD []

def uncell (w : Text) : Option Char := (TABLE.find? (·.2 = w)).map (·.1)

theorem uncell_cell : ∀ c ∈ KEYS, uncell (cell c) = some c := by decide +kernel

theorem lt128 : ∀ c ∈ KEYS, c.toNat < 128 := by decide +kernel

/-! ## The representation system -/

/-- The light: the code of each character in turn. Texts outside the alphabet get a formal
representation that no file displays as. -/
def render (t : Text) : List Text ⊕ Text := if t.all ok then .inl (t.map cell) else .inr t

def uncells : List Text → Option Text
  | [] => some []
  | w :: ws => (uncell w).bind fun c => (uncells ws).map (c :: ·)

def scan : List Text ⊕ Text → Option Text
  | .inl ws => uncells ws
  | .inr t => some t

theorem uncells_cells : ∀ t : Text, t.all ok = true → uncells (t.map cell) = some t
  | [], _ => rfl
  | c :: t, h => by
    simp only [List.all_cons, Bool.and_eq_true, ok, decide_eq_true_eq] at h
    simp only [List.map_cons, uncells, uncell_cell c h.1, Option.bind_some,
      uncells_cells t (by simpa only [ok, List.all_eq_true, decide_eq_true_eq] using h.2),
      Option.map_some]

theorem scan_render (t : Text) : scan (render t) = some t := by
  unfold render
  split
  · exact uncells_cells t ‹_›
  · rfl

/-- The library: everything before the call `blink(…)`. -/
def ENC : Text := (include_str "morse.py.inc").toList

def PRE : Text := ENC ++ "blink(".toList

/-- A file blinks the Morse code of the string that `blink` receives. -/
def Disp (f : Text) (p : List Text ⊕ Text) : Prop :=
  ∃ x c e, parseFile f = some (x, c) ∧ parseCodeWith PRE c = some e ∧
    (e.eval x).all ok = true ∧ p = render (e.eval x)

def system : System Text (List Text ⊕ Text) where
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
  disp_q t ht := by
    have h128 : t.all (·.toNat < 128) = true := by
      simp only [List.all_eq_true, ok, decide_eq_true_eq] at ht ⊢
      exact fun c hc => lt128 c (ht c hc)
    exact ⟨render t, ⟨t, showWith PRE, .var, parseFile_quoteWith PRE safe_show t h128,
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

/-- The engine's output: a Python program that blinks itself in Morse code. -/
def quine : Text := diagonal.quine

theorem quine_ok : quine.all ok = true := by decide +kernel

/-- **The Morse quine.** -/
theorem quine_correct : system.IsQuine quine := diagonal.isQuine safe_tmpl quine_ok

end QuineEngine.PythonMorse
