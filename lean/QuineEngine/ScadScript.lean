import QuineEngine.PyScript

/-!
# OpenSCAD files that rebuild their own text: the model

OpenSCAD has no `eval`, so the OpenSCAD quines are data + code files of a fixed shape:
```
s="x";
c
```
The first line binds the string `x` to `s`; the second line is the code `c`, which must be `pre`
followed by an expression and `);`, where `pre` is a quine-specific OpenSCAD library ending in a
module call such as `m(`. String literals hold printable ASCII except `"` and backslash, and the
escapes `\xHH` for characters 1–127. Expressions are `s`, `chr([n,…])`, or `str(…)` of these.
OpenSCAD's lexer drops raw newlines inside string literals, so the code is a single line.

The semantics is deliberately conservative: files of any other shape display nothing.
-/

namespace QuineEngine.ScadScript

open QuineEngine.PsScript (stripPrefix stripPrefix_append hexDigit hexVal hexVal_hexDigit)
open QuineEngine.PyScript (readUntil digitsVal)

abbrev Text := List Char

/-! ## String literals -/

/-- Characters allowed unescaped in a string literal: printable ASCII except `"` and backslash. -/
def rawOK (c : Char) : Bool := 32 ≤ c.toNat && c.toNat < 127 && c != '"' && c != '\\'

/-- Characters that `\xHH` can write: 1–127 (OpenSCAD reads `\x00` as a space). -/
def escOK (c : Char) : Bool := 0 < c.toNat && c.toNat < 128

/-- Read a string literal body up to the closing `"`. -/
def readStr : Text → Option (Text × Text)
  | [] => none
  | c :: r =>
    if c = '"' then some ([], r)
    else if c = '\\' then
      match r with
      | 'x' :: a :: b :: r' =>
        match hexVal a, hexVal b with
        | some x, some y =>
          if 0 < 16 * x + y ∧ 16 * x + y < 128 then
            (readStr r').map fun (s, r'') => (Char.ofNat (16 * x + y) :: s, r'')
          else none
        | _, _ => none
      | _ => none
    else if rawOK c then (readStr r).map fun (s, r') => (c :: s, r')
    else none

theorem readStr_raw (r : Text) : ∀ x : Text, x.all rawOK = true →
    readStr (x ++ '"' :: r) = some (x, r) := by
  intro x hx
  induction x with
  | nil =>
    rw [List.nil_append, readStr.eq_def]
    simp
  | cons c x ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hx
    have h1 : c ≠ '"' := fun h => by subst h; exact absurd hx.1 (by decide)
    have h2 : c ≠ '\\' := fun h => by subst h; exact absurd hx.1 (by decide)
    rw [List.cons_append, readStr.eq_def]
    simp only [if_neg h1, if_neg h2, hx.1, if_true, ih hx.2]
    rfl

/-- `\xHH` for each character. -/
def escs : Text → Text
  | [] => []
  | c :: t => '\\' :: 'x' :: hexDigit (c.toNat / 16) :: hexDigit (c.toNat % 16) :: escs t

theorem readStr_escs (r : Text) : ∀ t : Text, t.all escOK = true →
    readStr (escs t ++ '"' :: r) = some (t, r) := by
  intro t ht
  induction t with
  | nil =>
    rw [escs, List.nil_append, readStr.eq_def]
    simp
  | cons c t ih =>
    simp only [List.all_cons, Bool.and_eq_true] at ht
    have hc := ht.1
    simp only [escOK, Bool.and_eq_true, decide_eq_true_eq] at hc
    have h1 : c.toNat / 16 < 16 := Nat.lt_of_le_of_lt (Nat.div_le_div_right (Nat.le_of_lt hc.2))
      (by decide)
    have h2 : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    have hn : 16 * (c.toNat / 16) + c.toNat % 16 = c.toNat := Nat.div_add_mod _ _
    simp only [escs, List.cons_append]
    rw [readStr.eq_def]
    simp only [if_neg (show '\\' ≠ '"' by decide), if_pos, hexVal_hexDigit _ h1,
      hexVal_hexDigit _ h2, hn, if_pos (And.intro hc.1 hc.2), ih ht.2]
    simp [Char.ofNat_toNat]

/-! ## Files -/

def PRE : Text := ['s', '=', '"']
def MID : Text := ['"', ';', '\n']

/-- Parse a file into the value of `s` and the code. -/
def parseFile (f : Text) : Option (Text × Text) :=
  match stripPrefix PRE f with
  | some r =>
    match readStr r with
    | some (x, r) => (stripPrefix [';', '\n'] r).map (x, ·)
    | none => none
  | none => none

/-! ## The code -/

inductive Atom
  | var
  | chr (ns : List Nat)
  deriving DecidableEq

/-- An expression is `str` of its atoms, written as the bare atom when there is one. -/
abbrev Expr := List Atom

def Atom.eval (v : Text) : Atom → Text
  | var => v
  | chr ns => ns.map Char.ofNat

def Expr.eval (v : Text) (e : Expr) : Text := (e.map (Atom.eval v)).flatten

def nums : List Nat → Text
  | [] => []
  | [n] => (toString n).toList
  | n :: ns => (toString n).toList ++ ',' :: nums ns

def Atom.show : Atom → Text
  | var => ['s']
  | chr ns => "chr([".toList ++ (nums ns ++ [']', ')'])

def atoms : List Atom → Text
  | [] => []
  | [a] => a.show
  | a :: as => a.show ++ ',' :: atoms as

def Expr.show (e : Expr) : Text :=
  match e with
  | [a] => a.show
  | _ => "str(".toList ++ (atoms e ++ [')'])

def splitComma : Text → List Text
  | [] => [[]]
  | c :: r =>
    if c = ',' then [] :: splitComma r
    else match splitComma r with
      | d :: ds => (c :: d) :: ds
      | [] => [[c]]

/-- Numbers from 1 to 127, which `chr` maps to the characters with those codes. -/
def parseNums (ds : Text) : Option (List Nat) :=
  (splitComma ds).mapM fun d =>
    match digitsVal d with
    | some n => if 0 < n ∧ n < 128 then some n else none
    | none => none

def parseAtom (r : Text) : Option (Atom × Text) :=
  match r with
  | 's' :: r => some (.var, r)
  | _ =>
    match stripPrefix "chr([".toList r with
    | some r =>
      match readUntil ']' r with
      | some (ds, ')' :: r') => (parseNums ds).map fun ns => (.chr ns, r')
      | _ => none
    | none => none

def parseAtoms : Nat → Text → Option (List Atom × Text)
  | 0, _ => none
  | k + 1, r =>
    match parseAtom r with
    | some (a, ',' :: r') => (parseAtoms k r').map fun (as, r'') => (a :: as, r'')
    | some (a, r') => some ([a], r')
    | none => none

def parseExpr (r : Text) : Option (Expr × Text) :=
  match stripPrefix "str(".toList r with
  | some r =>
    match parseAtoms (r.length + 1) r with
    | some (as, ')' :: r') => some (as, r')
    | _ => none
  | none => (parseAtom r).map fun (a, r') => ([a], r')

/-- The code `pre E);`, where `pre` is a library followed by a call such as `m(`. -/
def codeWith (pre : Text) (e : Expr) : Text := pre ++ (e.show ++ [')', ';'])

/-- Parse code of the form `pre E);` into `E`. -/
def parseCodeWith (pre c : Text) : Option Expr :=
  match stripPrefix pre c with
  | some r =>
    match parseExpr r with
    | some (e, r') => if r' = [')', ';'] then some e else none
    | none => none
  | none => none

/-! ## Substitution, quotation and the template -/

/-- Texts that can be bound to `s` without escaping. -/
def safe (x : Text) : Bool := x.all rawOK

/-- `sub c x` binds `x` to `s` and runs the code `c`. -/
def sub (c x : Text) : Text := PRE ++ (x ++ (MID ++ c))

theorem parseFile_sub {c x : Text} (hx : safe x = true) : parseFile (sub c x) = some (x, c) := by
  unfold parseFile sub
  rw [stripPrefix_append]
  dsimp only
  rw [show MID ++ c = '"' :: ([';', '\n'] ++ c) from rfl, readStr_raw _ x hx]
  dsimp only
  rw [stripPrefix_append]
  rfl

/-- The code `pre s);`: show the value of `s`. -/
def showWith (pre : Text) : Text := codeWith pre [.var]

/-- A file that binds `t` (escaped) to `s` and shows it. -/
def quoteWith (pre t : Text) : Text := PRE ++ (escs t ++ (MID ++ showWith pre))

theorem parseFile_quoteWith (pre t : Text) (ht : t.all escOK = true) :
    parseFile (quoteWith pre t) = some (t, showWith pre) := by
  unfold parseFile quoteWith
  rw [stripPrefix_append]
  dsimp only
  rw [show MID ++ showWith pre = '"' :: ([';', '\n'] ++ showWith pre) from rfl,
    readStr_escs _ t ht]
  dsimp only
  rw [stripPrefix_append]
  rfl

/-- `str(chr([115,61,34]),s,chr([34,59,10]),s)`, that is `s="` ++ s ++ `";` ++ newline ++ s. -/
def tmplExpr : Expr := [.chr [115, 61, 34], .var, .chr [34, 59, 10], .var]

theorem eval_tmpl (x : Text) : tmplExpr.eval x = sub x x := by
  simp [Expr.eval, tmplExpr, Atom.eval, sub, PRE, MID]

/-- The template: show `sub s s`. -/
def tmplWith (pre : Text) : Text := codeWith pre tmplExpr

theorem escOK_sub {x : Text} (hx : safe x = true) : (sub x x).all escOK = true := by
  have h : x.all escOK = true := by
    simp only [safe, List.all_eq_true] at hx ⊢
    intro c hc
    have := hx c hc
    simp only [rawOK, Bool.and_eq_true, decide_eq_true_eq] at this
    simp only [escOK, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Nat.lt_of_lt_of_le (by decide) this.1.1.1, Nat.lt_trans this.1.1.2 (by decide)⟩
  simp only [sub, List.all_append, h]
  decide

end QuineEngine.ScadScript
