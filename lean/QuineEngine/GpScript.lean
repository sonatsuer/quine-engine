import QuineEngine.PyScript

/-!
# gnuplot scripts that evaluate their own text: the model

The gnuplot quines are one-line scripts of a fixed shape:
```
v='x';eval v          or          v='x';eval 'c'
```
Each binds the string `x` to `v` and evaluates the code `x` or `c`. String literals are `'…'`
with printable ASCII but no `'`, or `"…"` made of octal escapes `\ooo` of printable characters.
The evaluated code must be `s=E;` followed by `enc`, where `E` is an expression and `enc` is a
quine-specific gnuplot library that draws the string `s`. Expressions are concatenations (`.`) of
`"…"` literals, `v` and `sprintf("%c",n)`.

The semantics is deliberately conservative: files of any other shape display nothing.
-/

namespace QuineEngine.GpScript

open QuineEngine.PsScript (stripPrefix stripPrefix_append)
open QuineEngine.PyScript (readUntil readUntil_append digitsVal)

abbrev Text := List Char

/-! ## String literals -/

def printable (c : Char) : Bool := 32 ≤ c.toNat && c.toNat < 127

/-- Characters allowed in a `'…'` literal: printable ASCII except `'`. -/
def rawOK (c : Char) : Bool := printable c && c != '\''

/-- The literal `'x'`. -/
def lit (x : Text) : Text := '\'' :: (x ++ ['\''])

def octDigit (n : Nat) : Char := Char.ofNat (48 + n)

def octVal (c : Char) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 55 then some (c.toNat - 48) else none

theorem octVal_octDigit (n : Nat) (h : n < 8) : octVal (octDigit n) = some n := by
  have key : ∀ k : Fin 8, octVal (octDigit k) = some k := by decide
  exact key ⟨n, h⟩

/-- `\ooo` for each character. -/
def octs : Text → Text
  | [] => []
  | c :: t =>
    '\\' :: octDigit (c.toNat / 64) :: octDigit (c.toNat / 8 % 8) :: octDigit (c.toNat % 8) ::
      octs t

/-- Read the body of a `"…"` literal of octal escapes, up to its closing `"`. -/
def readOct : Text → Option (Text × Text)
  | [] => none
  | c :: r =>
    if c = '"' then some ([], r)
    else if c = '\\' then
      match r with
      | a :: b :: d :: r' =>
        match octVal a, octVal b, octVal d with
        | some x, some y, some z =>
          if 32 ≤ 64 * x + 8 * y + z ∧ 64 * x + 8 * y + z < 127 then
            (readOct r').map fun (s, r'') => (Char.ofNat (64 * x + 8 * y + z) :: s, r'')
          else none
        | _, _, _ => none
      | _ => none
    else none

theorem readOct_octs (r : Text) : ∀ t : Text, t.all printable = true →
    readOct (octs t ++ '"' :: r) = some (t, r) := by
  intro t ht
  induction t with
  | nil =>
    rw [octs, List.nil_append, readOct.eq_def]
    simp
  | cons c t ih =>
    simp only [List.all_cons, Bool.and_eq_true] at ht
    have hc := ht.1
    simp only [printable, Bool.and_eq_true, decide_eq_true_eq] at hc
    have h1 : c.toNat / 64 < 8 := by omega
    have h2 : c.toNat / 8 % 8 < 8 := Nat.mod_lt _ (by decide)
    have h3 : c.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
    have hn : 64 * (c.toNat / 64) + 8 * (c.toNat / 8 % 8) + c.toNat % 8 = c.toNat := by omega
    simp only [octs, List.cons_append]
    rw [readOct.eq_def]
    simp only [if_neg (show '\\' ≠ '"' by decide), if_true, octVal_octDigit _ h1,
      octVal_octDigit _ h2, octVal_octDigit _ h3, hn, if_pos (And.intro hc.1 hc.2), ih ht.2]
    simp [Char.ofNat_toNat]

/-- Read a literal: `'…'` or `"…"` in octal. -/
def readLit : Text → Option (Text × Text)
  | '\'' :: r =>
    match readUntil '\'' r with
    | some (x, r') => if x.all rawOK then some (x, r') else none
    | none => none
  | '"' :: r => readOct r
  | _ => none

theorem readLit_lit {x : Text} (hx : x.all rawOK = true) (r : Text) :
    readLit (lit x ++ r) = some (x, r) := by
  have hq : x.all (· ≠ '\'') = true := by
    simp only [List.all_eq_true, decide_eq_true_eq] at hx ⊢
    intro c hc h
    have := hx c hc
    subst h
    exact absurd this (by decide)
  simp only [lit, List.cons_append, List.append_assoc, readLit,
    readUntil_append _ _ x hq, hx, if_true, List.nil_append]

theorem readLit_octs {t : Text} (ht : t.all printable = true) (r : Text) :
    readLit (('"' :: (octs t ++ ['"'])) ++ r) = some (t, r) := by
  simp only [List.cons_append, List.append_assoc, readLit,
    readOct_octs _ t ht, List.nil_append]

/-! ## Files -/

def V : Text := ['v', '=']
def EVAL : Text := ";eval ".toList

/-- Parse a file into the value of `v` and the code that is evaluated. -/
def parseFile (f : Text) : Option (Text × Text) :=
  match stripPrefix V f with
  | some r =>
    match readLit r with
    | some (x, r) =>
      match stripPrefix EVAL r with
      | some r =>
        if r = ['v'] then some (x, x)
        else
          match readLit r with
          | some (c, []) => some (x, c)
          | _ => none
      | none => none
    | none => none
  | none => none

/-! ## The evaluated code -/

inductive Expr
  | str (s : Text)
  | var
  | chr (n : Nat)
  | add (e₁ e₂ : Expr)
  deriving DecidableEq

/-- The value of an expression when `v` holds the string `v`. -/
def Expr.eval (v : Text) : Expr → Text
  | str s => s
  | var => v
  | chr n => [Char.ofNat n]
  | add e₁ e₂ => e₁.eval v ++ e₂.eval v

/-- gnuplot source of an expression. -/
def Expr.show : Expr → Text
  | str s => '"' :: (s ++ ['"'])
  | var => ['v']
  | chr n => "sprintf(\"%c\",".toList ++ ((toString n).toList ++ [')'])
  | add e₁ e₂ => e₁.show ++ ('.' :: e₂.show)

/-- Characters allowed in a `"…"` atom: printable ASCII except `"`, `'` and backslash. -/
def strOK (d : Char) : Bool := printable d && d != '"' && d != '\'' && d != '\\'

def parseAtom : Text → Option (Expr × Text)
  | [] => none
  | c :: r =>
    if c = '"' then
      match readUntil '"' r with
      | some (s, r') => if s.all strOK then some (.str s, r') else none
      | none => none
    else if c = 'v' then some (.var, r)
    else
      match stripPrefix "printf(\"%c\",".toList r with
      | some r =>
        if c = 's' then
          match readUntil ')' r with
          | some (ds, r') =>
            match digitsVal ds with
            | some n => if 32 ≤ n ∧ n < 127 then some (.chr n, r') else none
            | none => none
          | none => none
        else none
      | none => none

def parseSum : Nat → Expr → Text → Option (Expr × Text)
  | 0, _, _ => none
  | _ + 1, acc, [] => some (acc, [])
  | k + 1, acc, c :: r =>
    if c = '.' then
      match parseAtom r with
      | some (e, r') => parseSum k (.add acc e) r'
      | none => none
    else some (acc, c :: r)

def parseExpr (s : Text) : Option (Expr × Text) :=
  match parseAtom s with
  | some (e, r) => parseSum (s.length + 1) e r
  | none => none

/-- The code `s=E;enc`: set `s` to the value of `E`, then run the library. -/
def codeWith (enc : Text) (e : Expr) : Text := 's' :: '=' :: (e.show ++ (';' :: enc))

/-- Parse evaluated code of the form `s=E;enc` into `E`. -/
def parseCodeWith (enc c : Text) : Option Expr :=
  match stripPrefix ['s', '='] c with
  | some r =>
    match parseExpr r with
    | some (e, r') => if r' = ';' :: enc then some e else none
    | none => none
  | none => none

/-! ## Substitution, quotation and the template -/

/-- Texts that can be bound to `v` without escaping. -/
def safe (x : Text) : Bool := x.all rawOK

/-- `sub c x` binds `x` to `v` and evaluates `c`; if `c = x` it evaluates `v` itself. -/
def sub (c x : Text) : Text := V ++ (lit x ++ (EVAL ++ (if c = x then ['v'] else lit c)))

theorem parseFile_sub {c x : Text} (hc : safe c = true) (hx : safe x = true) :
    parseFile (sub c x) = some (x, c) := by
  unfold parseFile sub
  rw [stripPrefix_append]
  dsimp only
  rw [readLit_lit hx]
  dsimp only
  rw [stripPrefix_append]
  dsimp only
  by_cases h : c = x
  · subst h
    simp
  · rw [if_neg h, if_neg (by unfold lit; simp), show lit c = lit c ++ [] from by simp,
      readLit_lit hc]

/-- The code `s=v;enc`: draw the value of `v`. -/
def showWith (enc : Text) : Text := codeWith enc .var

/-- A file that binds `t` (in octal) to `v` and draws it. -/
def quoteWith (enc t : Text) : Text :=
  V ++ (('"' :: (octs t ++ ['"'])) ++ (EVAL ++ lit (showWith enc)))

theorem parseFile_quoteWith (enc : Text) (hs : safe (showWith enc) = true) (t : Text)
    (ht : t.all printable = true) : parseFile (quoteWith enc t) = some (t, showWith enc) := by
  unfold parseFile quoteWith
  rw [stripPrefix_append]
  dsimp only
  rw [readLit_octs ht]
  dsimp only
  rw [stripPrefix_append]
  dsimp only
  rw [if_neg (by unfold lit; simp), show lit (showWith enc) = lit (showWith enc) ++ [] from by simp,
    readLit_lit hs]

/-- `v='` ++ v ++ `';eval v`, with `'` written as `sprintf("%c",39)`. -/
def tmplExpr : Expr :=
  .add (.add (.add (.add (.str "v=".toList) (.chr 39)) .var) (.chr 39)) (.str ";eval v".toList)

theorem eval_tmpl (x : Text) : tmplExpr.eval x = sub x x := by
  simp only [sub, if_pos, V, lit, EVAL, tmplExpr, Expr.eval, List.append_assoc, List.cons_append]
  rfl

/-- The template: draw `sub v v`. -/
def tmplWith (enc : Text) : Text := codeWith enc tmplExpr

theorem printable_sub {x : Text} (hx : safe x = true) : (sub x x).all printable = true := by
  have h : x.all printable = true := by
    simp only [safe, List.all_eq_true] at hx ⊢
    intro c hc
    have := hx c hc
    simp only [rawOK, Bool.and_eq_true] at this
    exact this.1
  simp only [sub, if_pos, lit, List.all_append, List.all_cons, h]
  decide

end QuineEngine.GpScript
