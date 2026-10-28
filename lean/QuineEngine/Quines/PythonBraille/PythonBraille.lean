import QuineEngine.Braille
import QuineEngine.PyScript

/-!
# A Python program that prints itself in braille

The program prints its own source in the North American Computer Braille Code (NABCC), the 8-dot
code of refreshable braille displays, as Unicode braille cells. Newlines stay newlines, so each
line of the source becomes one line of cells.

The file has the shape of `QuineEngine.PyScript`, and its library `ENC` is `braille.py.inc`,
which defines `braille`. The braille code is concrete: `cell` is NABCC on printable ASCII, and
`uncell` reads it back, so the theorem has no hypotheses. The library is trusted to print `render`
of its argument; `check.py` tests this against a NABCC table copied from liblouis.
-/

namespace QuineEngine.PythonBraille

open QuineEngine.PyScript QuineEngine.Braille

/-! ## NABCC -/

/-- The characters with a cell: newline and printable ASCII. -/
def ok (c : Char) : Bool := c = '\n' || (32 ≤ c.toNat && c.toNat < 127)

/-- The 8-dot cell of a printable character. Dot 7 marks `@`–`^`, which include the capitals;
lower case and `` ` ``–`~` take the cell of the character 32 below, without dot 7. -/
def dots (n : Nat) : Nat :=
  if n < 96 then ASCII.getD (n - 32) 0 + (if 64 ≤ n ∧ n < 95 then 64 else 0)
  else ASCII.getD (n - 64) 0

def cell (c : Char) : Char := if c = '\n' then c else Char.ofNat (0x2800 + dots c.toNat)

def ALPHABET : List Char := '\n' :: (List.range 95).map fun i => Char.ofNat (32 + i)

def uncell (b : Char) : Option Char := ALPHABET.find? fun c => cell c = b

theorem uncell_cell (c : Char) (h : ok c = true) : uncell (cell c) = some c := by
  have key : ∀ n : Fin 128, ok (Char.ofNat n) = true →
      uncell (cell (Char.ofNat n)) = some (Char.ofNat n) := by decide +kernel
  have hc : c.toNat < 128 := by
    simp only [ok, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · subst h
      decide
    · exact Nat.lt_trans h.2 (by decide)
  have := key ⟨c.toNat, hc⟩
  simp only [Char.ofNat_toNat] at this
  exact this h

/-! ## The representation system -/

/-- Texts outside the alphabet get a formal representation that no file displays as. -/
def render (t : Text) : Text ⊕ Text := if t.all ok then .inl (t.map cell) else .inr t

def uncells : Text → Option Text
  | [] => some []
  | b :: s => (uncell b).bind fun c => (uncells s).map (c :: ·)

def scan : Text ⊕ Text → Option Text
  | .inl s => uncells s
  | .inr t => some t

theorem uncells_cells : ∀ t : Text, t.all ok = true → uncells (t.map cell) = some t
  | [], _ => rfl
  | c :: t, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [uncells, uncell_cell c h.1, uncells_cells t h.2]

theorem scan_render (t : Text) : scan (render t) = some t := by
  unfold render
  split
  · exact uncells_cells t ‹_›
  · rfl

/-- The library: everything before the call `braille(…)`. -/
def ENC : Text := (include_str "braille.py.inc").toList

def PRE : Text := ENC ++ "braille(".toList

/-- A file prints the braille of the string that `braille` receives. -/
def Disp (f : Text) (p : Text ⊕ Text) : Prop :=
  ∃ x c e, parseFile f = some (x, c) ∧ parseCodeWith PRE c = some e ∧
    (e.eval x).all ok = true ∧ p = render (e.eval x)

def system : System Text (Text ⊕ Text) where
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
      simp only [List.all_eq_true, decide_eq_true_eq] at ht ⊢
      intro c hc
      have := ht c hc
      simp only [ok, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
      rcases this with h | h
      · subst h
        decide
      · exact Nat.lt_trans h.2 (by decide)
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

/-- The engine's output: a Python program that prints itself in braille. -/
def quine : Text := diagonal.quine

theorem quine_ok : quine.all ok = true := by decide +kernel

/-- **The braille quine.** -/
theorem quine_correct : system.IsQuine quine := diagonal.isQuine safe_tmpl quine_ok

end QuineEngine.PythonBraille
