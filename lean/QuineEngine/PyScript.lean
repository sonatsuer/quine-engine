import QuineEngine.PsScript

/-!
# Python files that execute their own text: the model

The Python quines are files of a fixed shape:
```
v="""x""";exec(v)          or          v="""x""";exec("""c""")
```
followed by a newline. Each binds the string `x` to `v` and executes the code `x` or `c`. String
literals are `"""…"""` with printable ASCII and newlines but no `"` or backslash, or
`bytes.fromhex("…").decode()` with an ASCII text in hexadecimal. The executed code must be `pre`
followed by an expression and `)`, where `pre` is a quine-specific Python library ending in a call
such as `f(`. Expressions are sums of `'…'` literals, `v` and `chr(n)`.

The semantics is deliberately conservative: files of any other shape display nothing.
-/

namespace QuineEngine.PyScript

open QuineEngine.PsScript (stripPrefix stripPrefix_append hexDigit hexVal hexOf hexVal_hexDigit)

abbrev Text := List Char

/-! ## Reading up to a delimiter -/

def readUntil (stop : Char) : Text → Option (Text × Text)
  | [] => none
  | c :: r =>
    if c = stop then some ([], r) else (readUntil stop r).map fun (s, r') => (c :: s, r')

theorem readUntil_append (stop : Char) (r : Text) : ∀ x : Text, x.all (· ≠ stop) = true →
    readUntil stop (x ++ stop :: r) = some (x, r) := by
  intro x hx
  induction x with
  | nil => simp [readUntil]
  | cons c x ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hx
    simp [readUntil, hx.1, ih hx.2]

/-! ## String literals -/

/-- Characters allowed in a `"""…"""` literal: printable ASCII and newline, but no `"` or
backslash. -/
def rawOK (c : Char) : Bool :=
  c = '\n' || (32 ≤ c.toNat && c.toNat < 127 && c != '"' && c != '\\')

def Q3 : Text := ['"', '"', '"']

/-- The literal `"""x"""`. -/
def lit (x : Text) : Text := Q3 ++ (x ++ Q3)

def HEXA : Text := "bytes.fromhex(\"".toList
def HEXB : Text := "\").decode()".toList

/-- The literal `bytes.fromhex("…").decode()`. -/
def hexLit (t : Text) : Text := HEXA ++ (hexOf t ++ HEXB)

/-- Read hexadecimal digits up to `"`. -/
def readHex : Text → Option (Text × Text)
  | [] => none
  | c :: r =>
    if c = '"' then some ([], r)
    else
      match r with
      | d :: r' =>
        match hexVal c, hexVal d with
        | some a, some b => (readHex r').map fun (s, r'') => (Char.ofNat (16 * a + b) :: s, r'')
        | _, _ => none
      | [] => none

theorem hexDigit_ne_quote (n : Nat) (h : n < 16) : hexDigit n ≠ '"' := by
  have key : ∀ k : Fin 16, hexDigit k ≠ '"' := by decide
  exact key ⟨n, h⟩

theorem readHex_hexOf (r : Text) : ∀ t : Text, t.all (·.toNat < 256) = true →
    readHex (hexOf t ++ '"' :: r) = some (t, r) := by
  intro t ht
  induction t with
  | nil =>
    rw [hexOf, List.nil_append, readHex.eq_def]
    simp
  | cons c t ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at ht
    have h1 : c.toNat / 16 < 16 := by omega
    have h2 : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    have hc : Char.ofNat (16 * (c.toNat / 16) + c.toNat % 16) = c := by
      rw [Nat.div_add_mod, Char.ofNat_toNat]
    simp only [hexOf, List.cons_append]
    rw [readHex.eq_def]
    simp only [if_neg (hexDigit_ne_quote _ h1), hexVal_hexDigit _ h1, hexVal_hexDigit _ h2,
      ih ht.2]
    simp [hc]

/-- Read a literal: `"""…"""` or `bytes.fromhex("…").decode()`. -/
def readLit (r : Text) : Option (Text × Text) :=
  match stripPrefix Q3 r with
  | some r =>
    match readUntil '"' r with
    | some (x, r') =>
      match stripPrefix ['"', '"'] r' with
      | some r'' => if x.all rawOK then some (x, r'') else none
      | none => none
    | none => none
  | none =>
    match stripPrefix HEXA r with
    | some r =>
      match readHex r with
      | some (t, r') =>
        match stripPrefix (HEXB.drop 1) r' with
        | some r'' => if t.all (·.toNat < 128) then some (t, r'') else none
        | none => none
      | none => none
    | none => none

theorem readLit_lit {x : Text} (hx : x.all rawOK = true) (r : Text) :
    readLit (lit x ++ r) = some (x, r) := by
  have hq : x.all (· ≠ '"') = true := by
    simp only [List.all_eq_true, decide_eq_true_eq] at hx ⊢
    intro c hc h
    have := hx c hc
    subst h
    exact absurd this (by decide)
  unfold readLit lit
  rw [List.append_assoc, stripPrefix_append, List.append_assoc,
    show Q3 ++ r = '"' :: (['"', '"'] ++ r) from rfl]
  dsimp only
  rw [readUntil_append _ _ x hq]
  simp only [stripPrefix_append, hx, if_true]

theorem readLit_hexLit {t : Text} (ht : t.all (·.toNat < 128) = true) (r : Text) :
    readLit (hexLit t ++ r) = some (t, r) := by
  have h256 : t.all (·.toNat < 256) = true := by
    simp only [List.all_eq_true, decide_eq_true_eq] at ht ⊢
    exact fun c hc => Nat.lt_trans (ht c hc) (by decide)
  unfold readLit hexLit
  rw [show stripPrefix Q3 ((HEXA ++ (hexOf t ++ HEXB)) ++ r) = none from rfl,
    List.append_assoc, stripPrefix_append, List.append_assoc,
    show HEXB ++ r = '"' :: (HEXB.drop 1 ++ r) from rfl]
  dsimp only
  rw [readHex_hexOf _ t h256]
  simp only [stripPrefix_append, ht, if_true]

/-! ## Files -/

def V : Text := ['v', '=']
def EXEC : Text := ";exec(".toList
def NL : Text := [')', '\n']

/-- Parse a file into the value of `v` and the code that is executed. -/
def parseFile (f : Text) : Option (Text × Text) :=
  match stripPrefix V f with
  | some r =>
    match readLit r with
    | some (x, r) =>
      match stripPrefix EXEC r with
      | some r =>
        if r = 'v' :: NL then some (x, x)
        else
          match readLit r with
          | some (c, r') => if r' = NL then some (x, c) else none
          | none => none
      | none => none
    | none => none
  | none => none

/-! ## The executed code -/

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

/-- Python source of an expression. -/
def Expr.show : Expr → Text
  | str s => '\'' :: (s ++ ['\''])
  | var => ['v']
  | chr n => "chr(".toList ++ ((toString n).toList ++ [')'])
  | add e₁ e₂ => e₁.show ++ ('+' :: e₂.show)

def digitsVal (ds : Text) : Option Nat :=
  if ds ≠ [] ∧ ds.all Char.isDigit = true then
    some (ds.foldl (fun n d => 10 * n + (d.toNat - 48)) 0)
  else none

/-- Characters allowed in a `'…'` literal: printable ASCII except `'` and backslash. -/
def strOK (d : Char) : Bool := 32 ≤ d.toNat && d.toNat < 127 && d != '\'' && d != '\\'

def parseAtom : Text → Option (Expr × Text)
  | [] => none
  | c :: r =>
    if c = '\'' then
      match readUntil '\'' r with
      | some (s, r') => if s.all strOK then some (.str s, r') else none
      | none => none
    else if c = 'v' then some (.var, r)
    else
      match stripPrefix "hr(".toList r with
      | some r =>
        if c = 'c' then
          match readUntil ')' r with
          | some (ds, r') =>
            match digitsVal ds with
            | some n => if n < 128 then some (.chr n, r') else none
            | none => none
          | none => none
        else none
      | none => none

def parseSum : Nat → Expr → Text → Option (Expr × Text)
  | 0, _, _ => none
  | _ + 1, acc, [] => some (acc, [])
  | k + 1, acc, c :: r =>
    if c = '+' then
      match parseAtom r with
      | some (e, r') => parseSum k (.add acc e) r'
      | none => none
    else some (acc, c :: r)

def parseExpr (s : Text) : Option (Expr × Text) :=
  match parseAtom s with
  | some (e, r) => parseSum (s.length + 1) e r
  | none => none

/-- The code `pre E)`, where `pre` is a library followed by a call such as `f(`. -/
def codeWith (pre : Text) (e : Expr) : Text := pre ++ (e.show ++ [')'])

/-- Parse executed code of the form `pre E)` into `E`. -/
def parseCodeWith (pre c : Text) : Option Expr :=
  match stripPrefix pre c with
  | some r =>
    match parseExpr r with
    | some (e, r') => if r' = [')'] then some e else none
    | none => none
  | none => none

/-! ## Substitution, quotation and the template -/

/-- Texts that can be bound to `v` without escaping. -/
def safe (x : Text) : Bool := x.all rawOK

/-- `sub c x` binds `x` to `v` and executes `c`; if `c = x` it executes `v` itself. -/
def sub (c x : Text) : Text := V ++ (lit x ++ (EXEC ++ ((if c = x then ['v'] else lit c) ++ NL)))

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
  · rw [if_neg h, if_neg (by unfold lit Q3; simp), readLit_lit hc]
    simp

/-- The code `pre v)`: show the value of `v`. -/
def showWith (pre : Text) : Text := codeWith pre .var

/-- A file that binds `t` (in hexadecimal) to `v` and shows it. -/
def quoteWith (pre t : Text) : Text := V ++ (hexLit t ++ (EXEC ++ (lit (showWith pre) ++ NL)))

theorem parseFile_quoteWith (pre : Text) (hs : safe (showWith pre) = true) (t : Text)
    (ht : t.all (·.toNat < 128) = true) :
    parseFile (quoteWith pre t) = some (t, showWith pre) := by
  unfold parseFile quoteWith
  rw [stripPrefix_append]
  dsimp only
  rw [readLit_hexLit ht]
  dsimp only
  rw [stripPrefix_append]
  dsimp only
  rw [if_neg (by unfold lit Q3; simp), readLit_lit hs]
  simp

/-- `v="""` ++ v ++ `""";exec(v)` and a newline, with `"` and the newline written as `chr`. -/
def tmplExpr : Expr :=
  .add (.add (.add (.add (.add (.add (.add (.add (.add
    (.str "v=".toList) (.chr 34)) (.chr 34)) (.chr 34))
    .var)
    (.chr 34)) (.chr 34)) (.chr 34))
    (.str ";exec(v)".toList))
    (.chr 10)

theorem eval_tmpl (x : Text) : tmplExpr.eval x = sub x x := by
  simp only [sub, if_pos, V, lit, Q3, EXEC, NL, tmplExpr, Expr.eval, List.append_assoc]
  rfl

/-- The template: show `sub v v`. -/
def tmplWith (pre : Text) : Text := codeWith pre tmplExpr

theorem all128_of_safe {x : Text} (hx : safe x = true) : x.all (·.toNat < 128) = true := by
  simp only [safe, List.all_eq_true] at hx
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro c hc
  have := hx c hc
  simp only [rawOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
  rcases this with h | h
  · subst h
    decide
  · exact Nat.lt_trans h.1.1.2 (by decide)

theorem all128_sub {x : Text} (hx : safe x = true) : (sub x x).all (·.toNat < 128) = true := by
  have h := all128_of_safe hx
  simp only [sub, if_pos, lit, List.all_append, h]
  decide

end QuineEngine.PyScript
