import QuineEngine.Engine

/-!
# PostScript files that execute their own text: the shared model

The PostScript quines are files of a fixed shape:
```
%!PS
(x)dup cvx exec          or          (x)(c)cvx exec          or          <hex>(c)cvx exec
```
Each pushes the string `x` and executes the code `x` or `c` with that string on the stack. String
literals are `(…)` with balanced parentheses and no backslash, or `<…>` in hexadecimal. The
executed code must be `ENC` followed by a tail of `<hex>`, `exch` and `cat`, ending in
`Q showpage`, where `ENC` is a quine-specific PostScript library that defines `cat` (concatenate
two strings) and `Q` (draw the string on the stack). Files end with a newline, which document
viewers based on libspectre require.

This module holds everything that does not depend on the library. The semantics is deliberately
conservative: files of any other shape display nothing.
-/

namespace QuineEngine.PsScript

abbrev Text := List Char

/-! ## Parsing helpers -/

def stripPrefix : Text → Text → Option Text
  | [], s => some s
  | c :: p, d :: s => if c = d then stripPrefix p s else none
  | _ :: _, [] => none

theorem stripPrefix_append (p s : Text) : stripPrefix p (p ++ s) = some s := by
  induction p with
  | nil => rfl
  | cons c p ih => simp [stripPrefix, ih]

/-! ## Raw string literals `(…)` -/

/-- Characters allowed unescaped in a raw literal: printable ASCII except backslash. -/
def rawOK (c : Char) : Bool := 32 ≤ c.toNat && c.toNat < 127 && c != '\\'

/-- Parenthesis depth; `none` if it goes negative. -/
def walk : Nat → Text → Option Nat
  | d, [] => some d
  | d, c :: r =>
    if c = '(' then walk (d + 1) r
    else if c = ')' then (match d with | 0 => none | d + 1 => walk d r)
    else walk d r

/-- Read a raw literal body at depth `d`, up to the `)` that closes it. -/
def readRaw : Nat → Text → Option (Text × Text)
  | _, [] => none
  | d, c :: r =>
    if c = ')' then
      match d with
      | 0 => some ([], r)
      | d + 1 => (readRaw d r).map fun (s, r') => (c :: s, r')
    else if c = '(' then (readRaw (d + 1) r).map fun (s, r') => (c :: s, r')
    else if rawOK c then (readRaw d r).map fun (s, r') => (c :: s, r')
    else none

/-- Texts that can sit unescaped in a raw literal. -/
def safe (x : Text) : Bool := x.all rawOK && walk 0 x == some 0

theorem readRaw_balanced (rest : Text) : ∀ (x : Text) (d : Nat), x.all rawOK = true →
    walk d x = some 0 → readRaw d (x ++ ')' :: rest) = some (x, rest) := by
  intro x
  induction x with
  | nil =>
    intro d _ h
    simp [walk] at h
    subst h
    simp [readRaw]
  | cons c x ih =>
    intro d hall h
    simp only [List.all_cons, Bool.and_eq_true] at hall
    by_cases h1 : c = ')'
    · subst h1
      cases d with
      | zero => simp [walk] at h
      | succ d =>
        simp [walk] at h
        simp [readRaw, ih d hall.2 h]
    · by_cases h2 : c = '('
      · subst h2
        simp [walk] at h
        simp [readRaw, ih (d + 1) hall.2 h]
      · simp only [walk, if_neg h2, if_neg h1] at h
        simp [readRaw, h1, h2, hall.1, ih d hall.2 h]

theorem readRaw_safe {x : Text} (h : safe x = true) (rest : Text) :
    readRaw 0 (x ++ ')' :: rest) = some (x, rest) := by
  simp only [safe, Bool.and_eq_true, beq_iff_eq] at h
  exact readRaw_balanced rest x 0 h.1 h.2

/-! ## Hexadecimal literals `<…>` -/

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hexVal (c : Char) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then some (c.toNat - 87)
  else none

theorem hexVal_hexDigit (n : Nat) (h : n < 16) : hexVal (hexDigit n) = some n := by
  have key : ∀ k : Fin 16, hexVal (hexDigit k) = some k := by decide
  exact key ⟨n, h⟩

theorem hexDigit_ne_gt (n : Nat) (h : n < 16) : hexDigit n ≠ '>' := by
  have key : ∀ k : Fin 16, hexDigit k ≠ '>' := by decide
  exact key ⟨n, h⟩

/-- Two lowercase hexadecimal digits per character. -/
def hexOf : Text → Text
  | [] => []
  | c :: t => hexDigit (c.toNat / 16) :: hexDigit (c.toNat % 16) :: hexOf t

/-- Read a hex literal body up to `>`. -/
def readHex : Text → Option (Text × Text)
  | [] => none
  | c :: r =>
    if c = '>' then some ([], r)
    else
      match r with
      | d :: r' =>
        match hexVal c, hexVal d with
        | some a, some b => (readHex r').map fun (s, r'') => (Char.ofNat (16 * a + b) :: s, r'')
        | _, _ => none
      | [] => none

theorem readHex_hexOf (r : Text) : ∀ t : Text, t.all (·.toNat < 256) = true →
    readHex (hexOf t ++ '>' :: r) = some (t, r) := by
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
    simp only [if_neg (hexDigit_ne_gt _ h1), hexVal_hexDigit _ h1, hexVal_hexDigit _ h2, ih ht.2]
    simp [hc]

/-- A literal: raw `(…)` or hexadecimal `<…>`. -/
def readLit : Text → Option (Text × Text)
  | '(' :: r => readRaw 0 r
  | '<' :: r => readHex r
  | _ => none

/-! ## Files -/

def HDR : Text := "%!PS\n".toList

/-- Parse a file into the string on the stack and the code that is executed. -/
def parseFile (f : Text) : Option (Text × Text) :=
  match stripPrefix HDR f with
  | some r =>
    match readLit r with
    | some (s, r) =>
      if r = "dup cvx exec\n".toList then some (s, s)
      else
        match readLit r with
        | some (c, r') => if r' = "cvx exec\n".toList then some (s, c) else none
        | none => none
    | none => none
  | none => none

/-! ## The executed code -/

inductive Op
  | push (s : Text)
  | exch
  | cat
  deriving DecidableEq

def runOps : List Op → List Text → Option (List Text)
  | [], st => some st
  | .push s :: ops, st => runOps ops (s :: st)
  | .exch :: ops, a :: b :: st => runOps ops (b :: a :: st)
  | .cat :: ops, b :: a :: st => runOps ops ((a ++ b) :: st)
  | _, _ => none

/-- Parse a tail of ` <hex>`, ` exch` and ` cat` ending in ` Q showpage`. -/
def parseOps : Nat → Text → Option (List Op)
  | 0, _ => none
  | n + 1, r =>
    if r = " Q showpage".toList then some []
    else match r with
      | ' ' :: '<' :: r =>
        match readHex r with
        | some (s, r') => (parseOps n r').map (.push s :: ·)
        | none => none
      | ' ' :: 'e' :: 'x' :: 'c' :: 'h' :: r => (parseOps n r).map (.exch :: ·)
      | ' ' :: 'c' :: 'a' :: 't' :: r => (parseOps n r).map (.cat :: ·)
      | _ => none

/-- Parse executed code of the form `enc` followed by a tail. -/
def parseCodeWith (enc c : Text) : Option (List Op) :=
  match stripPrefix enc c with
  | some r => parseOps (r.length + 1) r
  | none => none

/-! ## Substitution, quotation and the template -/

/-- `sub c x` pushes `x` and executes `c`; if `c = x` it executes the pushed string itself. -/
def sub (c x : Text) : Text :=
  HDR ++ ('(' :: (x ++ (')' :: ((if c = x then "dup ".toList else '(' :: (c ++ [')'])) ++
    "cvx exec\n".toList))))

/-- The code `enc Q showpage`: draw the string on the stack. -/
def showWith (enc : Text) : Text := enc ++ " Q showpage".toList

/-- A file that pushes `t` in hexadecimal and draws it. -/
def quoteWith (enc t : Text) : Text :=
  HDR ++ ('<' :: (hexOf t ++ ('>' :: ('(' :: (showWith enc ++ (')' :: "cvx exec\n".toList))))))

/-- The two constant parts of `sub x x`, around `x`. -/
def preA : Text := HDR ++ ['(']
def preB : Text := ")dup cvx exec\n".toList

/-- The template: build `sub v v` from the string `v` on the stack, and draw it. -/
def tmplWith (enc : Text) : Text :=
  enc ++ " <".toList ++ hexOf preA ++ "> exch cat <".toList ++ hexOf preB ++
    "> cat Q showpage".toList

/-- The tail of the template. -/
def tmplOps : List Op := [.push preA, .exch, .cat, .push preB, .cat]

theorem parseFile_sub {c x : Text} (hc : safe c = true) (hx : safe x = true) :
    parseFile (sub c x) = some (x, c) := by
  unfold parseFile sub
  rw [stripPrefix_append]
  dsimp only
  rw [show ∀ r, readLit ('(' :: r) = readRaw 0 r from fun _ => rfl, readRaw_safe hx]
  dsimp only
  by_cases h : c = x
  · subst h
    simp
  · rw [if_neg h, if_neg (by simp)]
    rw [List.cons_append, show ∀ r, readLit ('(' :: r) = readRaw 0 r from fun _ => rfl,
      List.append_assoc, List.singleton_append, readRaw_safe hc]
    simp

theorem parseFile_quoteWith (enc : Text) (hs : safe (showWith enc) = true) (t : Text)
    (ht : t.all (·.toNat < 256) = true) :
    parseFile (quoteWith enc t) = some (t, showWith enc) := by
  unfold parseFile quoteWith
  rw [stripPrefix_append]
  dsimp only
  rw [show ∀ r, readLit ('<' :: r) = readHex r from fun _ => rfl, readHex_hexOf _ t ht]
  dsimp only
  rw [if_neg (by simp), show ∀ r, readLit ('(' :: r) = readRaw 0 r from fun _ => rfl,
    readRaw_safe hs]
  simp

theorem runOps_tmpl (x : Text) :
    runOps tmplOps [x] = some [sub x x] := by
  simp [runOps, tmplOps, sub, preA, preB]

theorem all256_of_safe {x : Text} (hx : safe x = true) : x.all (·.toNat < 256) = true := by
  simp only [safe, Bool.and_eq_true, List.all_eq_true] at hx
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro c hc
  have := hx.1 c hc
  simp only [rawOK, Bool.and_eq_true, decide_eq_true_eq] at this
  omega

theorem all256_sub {x : Text} (hx : safe x = true) : (sub x x).all (·.toNat < 256) = true := by
  have h := all256_of_safe hx
  simp only [sub, if_pos, List.all_append, List.all_cons, h]
  decide

end QuineEngine.PsScript
