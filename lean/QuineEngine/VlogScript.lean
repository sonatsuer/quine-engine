import QuineEngine.PsScript
import QuineEngine.Uart

/-!
# Verilog files that send their own text: the model

Verilog has no `eval`, so the Verilog quine is a data + code file of the fixed shape
```
`define s "x"
c
```
The first line defines the macro `s` as a string literal. The literal holds printable ASCII, with
`\n`, `\"` and `\\` for a line break, a quote and a backslash, so the code can be ordinary
multi-line Verilog. The rest of the file is the code `c`.

The model recognises two codes, which differ in one parameter (`full = 1` or `full = 0`):
- **the template.** The circuit sends, on its pin, the whole file `sub s s` rebuilt from the data
  `s`: the `define` line with `s` escaped, then `s` itself;
- **the show code.** The circuit sends `s` alone.

Files with any other code display nothing. The representation is a sequence of UART frames, as in
`QuineEngine.Uart`.
-/

namespace QuineEngine.VlogScript

open QuineEngine.PsScript (stripPrefix stripPrefix_append)

abbrev Text := List Char

/-! ## String literals -/

/-- Characters a literal can hold: printable ASCII and the line break. -/
def ok (c : Char) : Bool := (32 ≤ c.toNat && c.toNat < 127) || c = '\n'

/-- The body of a literal: `\n`, `\"` and `\\` for a line break, a quote and a backslash. -/
def esc : Text → Text
  | [] => []
  | c :: t =>
    if c = '\n' then '\\' :: 'n' :: esc t
    else if c = '"' then '\\' :: '"' :: esc t
    else if c = '\\' then '\\' :: '\\' :: esc t
    else c :: esc t

/-- Read a literal's body up to its closing `"`. -/
def readStr : Text → Option (Text × Text)
  | [] => none
  | c :: r =>
    if c = '"' then some ([], r)
    else if c = '\\' then
      match r with
      | 'n' :: r' => (readStr r').map fun (s, r'') => ('\n' :: s, r'')
      | '"' :: r' => (readStr r').map fun (s, r'') => ('"' :: s, r'')
      | '\\' :: r' => (readStr r').map fun (s, r'') => ('\\' :: s, r'')
      | _ => none
    else if 32 ≤ c.toNat ∧ c.toNat < 127 then (readStr r).map fun (s, r') => (c :: s, r')
    else none

theorem readStr_esc (r : Text) : ∀ t : Text, t.all ok = true →
    readStr (esc t ++ '"' :: r) = some (t, r) := by
  intro t ht
  induction t with
  | nil =>
    rw [esc, List.nil_append, readStr.eq_def]
    simp
  | cons c t ih =>
    simp only [List.all_cons, Bool.and_eq_true] at ht
    have hc := ht.1
    have ih := ih ht.2
    by_cases h1 : c = '\n'
    · subst h1
      simp only [esc, if_pos, List.cons_append]
      rw [readStr.eq_def]
      simp [ih]
    by_cases h2 : c = '"'
    · subst h2
      simp only [esc, if_neg (show '"' ≠ '\n' by decide), if_pos, List.cons_append]
      rw [readStr.eq_def]
      simp [ih]
    by_cases h3 : c = '\\'
    · subst h3
      simp only [esc, if_neg (show '\\' ≠ '\n' by decide), if_neg (show '\\' ≠ '"' by decide),
        if_pos, List.cons_append]
      rw [readStr.eq_def]
      simp [ih]
    have hp : 32 ≤ c.toNat ∧ c.toNat < 127 := by
      simp only [ok, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.resolve_right h1
    simp only [esc, if_neg h1, if_neg h2, if_neg h3, List.cons_append]
    rw [readStr.eq_def]
    simp [h2, h3, hp, ih]

theorem ok_esc : ∀ t : Text, t.all ok = true → (esc t).all ok = true
  | [], _ => rfl
  | c :: t, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := ok_esc t h.2
    unfold esc
    split
    · simp [ih]; decide
    split
    · simp [ih]; decide
    split
    · simp [ih]; decide
    · simp [h.1, ih]

/-! ## Files -/

/-- The first line up to the literal's body. -/
def DEF : Text := "`define s \"".toList

/-- `sub c x`: the data `x`, then the code `c`. -/
def sub (c x : Text) : Text := DEF ++ (esc x ++ ('"' :: '\n' :: c))

/-- Parse a file into its data and its code. -/
def parseFile (f : Text) : Option (Text × Text) :=
  match stripPrefix DEF f with
  | some r =>
    match readStr r with
    | some (x, '\n' :: c) => some (x, c)
    | _ => none
  | none => none

theorem parseFile_sub {x : Text} (hx : x.all ok = true) (c : Text) :
    parseFile (sub c x) = some (x, c) := by
  unfold parseFile sub
  rw [stripPrefix_append]
  dsimp only
  rw [readStr_esc _ x hx]
  rfl

theorem ok_sub {x : Text} (hx : x.all ok = true) : (sub x x).all ok = true := by
  unfold sub
  simp only [List.all_append, List.all_cons, ok_esc x hx, hx]
  decide

/-! ## The codes -/

/-- The code, split around its one-character parameter `full`. -/
structure Parts where
  pre : Text
  post : Text

variable (P : Parts)

/-- The template: `full = 1`, which sends the whole file. -/
def tmplCode : Text := P.pre ++ ('1' :: P.post)

/-- The show code: `full = 0`, which sends the data alone. -/
def showCode : Text := P.pre ++ ('0' :: P.post)

theorem showCode_ne : showCode P ≠ tmplCode P := by
  unfold showCode tmplCode
  intro h
  have := List.append_cancel_left h
  simp at this

/-- What the circuit sends, for a recognised code. -/
def evalCode (code data : Text) : Option Text :=
  if code = tmplCode P then some (sub data data)
  else if code = showCode P then some data
  else none

/-! ## The system -/

def Disp (f : Text) (p : List (List Bool) ⊕ Text) : Prop :=
  ∃ d c out, parseFile f = some (d, c) ∧ evalCode P c d = some out ∧ out ≠ [] ∧
    out.all ok = true ∧ p = Uart.render out

def system : System Text (List (List Bool) ⊕ Text) where
  disp := Disp P
  scan := Uart.scan
  render := Uart.render
  scan_render := Uart.scan_render

def quotation : Quotation (system P) where
  Dom t := t ≠ [] ∧ t.all ok = true
  q := sub (showCode P)
  disp_q t ht := by
    refine ⟨Uart.render t, ⟨t, showCode P, t, parseFile_sub ht.2 _, ?_, ht.1, ht.2, rfl⟩, rfl⟩
    unfold evalCode
    rw [if_neg (showCode_ne P), if_pos rfl]

def diagonal : Diagonal (system P) (quotation P) where
  sub := sub
  a := tmplCode P
  Ok x := x.all ok = true
  spec := by
    intro x hx s ⟨p, hd, hs⟩
    obtain ⟨d, c, out, hf, he, hne, hok, hp⟩ := hd
    change parseFile (sub (showCode P) (sub x x)) = _ at hf
    rw [parseFile_sub (ok_sub hx)] at hf
    cases hf
    unfold evalCode at he
    rw [if_neg (showCode_ne P), if_pos rfl] at he
    cases he
    subst hp
    change Uart.scan (Uart.render (sub x x)) = _ at hs
    rw [Uart.scan_render] at hs
    cases hs
    refine ⟨Uart.render (sub x x), ⟨x, tmplCode P, sub x x, parseFile_sub hx _, ?_, hne, hok, rfl⟩,
      Uart.scan_render _⟩
    unfold evalCode
    rw [if_pos rfl]

/-- The engine's fixed point. -/
def quine : Text := sub (tmplCode P) (tmplCode P)

theorem quine_correct (hok : (quine P).all ok = true) : (system P).IsQuine (quine P) := by
  have ha : (tmplCode P).all ok = true := by
    have h := hok
    unfold quine sub at h
    simp only [List.all_append, List.all_cons, Bool.and_eq_true] at h
    exact h.2.2.2.2
  refine (diagonal P).isQuine ha ⟨?_, hok⟩
  show sub (tmplCode P) (tmplCode P) ≠ []
  unfold sub DEF
  simp

end QuineEngine.VlogScript
