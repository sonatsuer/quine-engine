import QuineEngine.Engine

/-!
# SVG files with a script: the shared model

The SVG quines are files of the fixed shape
```
<svg xmlns='http://www.w3.org/2000/svg'><script>v="x";eval(arg)</script></svg>
```
which bind the string literal `x` to `v` and evaluate `arg`, either `v` itself or a string literal.
The evaluated code is `pre E)`, where `pre` is a quine-specific prefix (an opaque JavaScript
library followed by the name of its drawing function and `(`) and `E` is an expression built from
string literals, `v`, `H(n)` (that is, `String.fromCharCode(n)`) and `+`.

This module holds everything that does not depend on the library: the file and literal parsers,
escaping, the XML automaton, the expression fragment, substitution, quotation and the template,
with their lemmas. The semantics is deliberately conservative: files that do not parse display
nothing. It is faithful for the files it accepts, because their script text contains no `<` or
`&` and no `]]>` (so the XML parser passes it through unchanged) and their string literals use
only printable characters and `\xHH` escapes.
-/

namespace QuineEngine.SvgScript

abbrev Text := List Char

/-! ## Parsing helpers -/

def stripPrefix : Text → Text → Option Text
  | [], s => some s
  | c :: p, d :: s => if c = d then stripPrefix p s else none
  | _ :: _, [] => none

def stripSuffix (suf s : Text) : Option Text :=
  (stripPrefix suf.reverse s.reverse).map List.reverse

theorem stripPrefix_append (p s : Text) : stripPrefix p (p ++ s) = some s := by
  induction p with
  | nil => rfl
  | cons c p ih => simp [stripPrefix, ih]

theorem stripSuffix_append (b suf : Text) : stripSuffix suf (b ++ suf) = some b := by
  simp [stripSuffix, List.reverse_append, stripPrefix_append]

/-! ## JavaScript string literals -/

/-- Characters that may appear unescaped in a string literal. -/
def rawOK (c : Char) : Bool :=
  32 ≤ c.toNat && c.toNat < 127 && c != '"' && c != '\\'

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hexVal (c : Char) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then some (c.toNat - 87)
  else none

/-- Read a string literal body up to its closing `"`, decoding `\xHH` escapes. -/
def readLit : Text → Option (Text × Text)
  | [] => none
  | c :: r =>
    if c = '"' then some ([], r)
    else if c = '\\' then
      match r with
      | 'x' :: h :: l :: r => do
        let a ← hexVal h
        let b ← hexVal l
        let (s, r') ← readLit r
        some (Char.ofNat (16 * a + b) :: s, r')
      | _ => none
    else if rawOK c then (readLit r).map fun (s, r') => (c :: s, r')
    else none

/-- Escape a character for a string literal; `<`, `&` and `>` are escaped for XML. -/
def escChar (c : Char) : Text :=
  if rawOK c && c != '<' && c != '&' && c != '>' then [c]
  else ['\\', 'x', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]

def esc : Text → Text
  | [] => []
  | c :: t => escChar c ++ esc t

theorem hexVal_hexDigit (n : Nat) (h : n < 16) : hexVal (hexDigit n) = some n := by
  have key : ∀ k : Fin 16, hexVal (hexDigit k) = some k := by decide
  exact key ⟨n, h⟩

theorem readLit_raw (r : Text) : ∀ x : Text, x.all rawOK = true →
    readLit (x ++ '"' :: r) = some (x, r) := by
  intro x hx
  induction x with
  | nil => rw [List.nil_append, readLit.eq_def]; simp
  | cons c x ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hx
    have hc := hx.1
    simp only [rawOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
    rw [List.cons_append, readLit.eq_def]
    simp [hc.2, hc.1.2, hx.1, ih hx.2]

theorem readLit_esc (r : Text) : ∀ t : Text, t.all (·.toNat < 256) = true →
    readLit (esc t ++ '"' :: r) = some (t, r) := by
  intro t ht
  induction t with
  | nil => rw [esc, List.nil_append, readLit.eq_def]; simp
  | cons c t ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at ht
    have ih := ih ht.2
    simp only [esc, escChar]
    split
    · rename_i h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      have hc := h.1.1.1
      simp only [rawOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
      rw [List.singleton_append, List.cons_append, readLit.eq_def]
      simp [hc.2, hc.1.2, h.1.1.1, ih]
    · have h1 : c.toNat / 16 < 16 := by omega
      have h2 : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
      have hc : Char.ofNat (16 * (c.toNat / 16) + c.toNat % 16) = c := by
        rw [Nat.div_add_mod, Char.ofNat_toNat]
      simp only [List.cons_append, List.nil_append]
      rw [readLit.eq_def]
      simp [hexVal_hexDigit _ h1, hexVal_hexDigit _ h2, ih, hc]

/-! ## XML safety of the script text

The script text must not contain `<`, `&` or `]]>`. The state counts trailing `]`s (up to 2). -/

def xmlStep (s : Nat) (c : Char) : Option Nat :=
  if c = '<' ∨ c = '&' then none
  else if c = ']' then some (min (s + 1) 2)
  else if c = '>' then (if s = 2 then none else some 0)
  else some 0

def xmlRun : Nat → Text → Option Nat
  | s, [] => some s
  | s, c :: r => (xmlStep s c).bind fun s' => xmlRun s' r

theorem xmlRun_append (s : Nat) (u w : Text) :
    xmlRun s (u ++ w) = (xmlRun s u).bind fun s' => xmlRun s' w := by
  induction u generalizing s with
  | nil => rfl
  | cons c u ih =>
    simp only [List.cons_append, xmlRun]
    cases xmlStep s c <;> simp [ih]

theorem xmlRun_quote (s : Nat) (w : Text) : xmlRun s ('"' :: w) = xmlRun 0 w := by
  simp [xmlRun, xmlStep]

theorem xmlStep_plain (s : Nat) (c : Char) (h1 : c ≠ '<') (h2 : c ≠ '&') (h3 : c ≠ ']')
    (h4 : c ≠ '>') : xmlStep s c = some 0 := by
  simp [xmlStep, h1, h2, h3, h4]

theorem xmlRun_esc (t : Text) (ht : t.all (·.toNat < 256) = true) :
    ∀ s, (xmlRun s (esc t)).isSome := by
  have hex : ∀ k : Fin 16, hexDigit k ≠ '<' ∧ hexDigit k ≠ '&' ∧ hexDigit k ≠ ']' ∧
      hexDigit k ≠ '>' := by decide
  induction t with
  | nil => intro s; rfl
  | cons c t ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at ht
    intro s
    simp only [esc, escChar, xmlRun_append]
    split
    · rename_i h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      have step : (xmlStep s c).isSome := by
        unfold xmlStep
        simp only [h.1.1.2, h.1.2, false_or, if_false]
        split
        · rfl
        · simp [h.2]
      obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.1 step
      simp [xmlRun, hs', ih ht.2]
    · have d1 := hex ⟨c.toNat / 16, by omega⟩
      have d2 := hex ⟨c.toNat % 16, Nat.mod_lt _ (by decide)⟩
      simp only at d1 d2
      have e : xmlRun s ['\\', 'x', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)] = some 0 := by
        simp only [xmlRun, xmlStep_plain _ '\\' (by decide) (by decide) (by decide) (by decide),
          xmlStep_plain _ 'x' (by decide) (by decide) (by decide) (by decide),
          xmlStep_plain _ _ d1.1 d1.2.1 d1.2.2.1 d1.2.2.2,
          xmlStep_plain _ _ d2.1 d2.2.1 d2.2.2.1 d2.2.2.2, Option.bind_some]
      rw [e, Option.bind_some]
      exact ih ht.2 0

/-! ## Files -/

def PRE : Text := "<svg xmlns='http://www.w3.org/2000/svg'><script>".toList
def SUF : Text := "</script></svg>".toList

/-- The script text: bind the literal `lit` to `v`, then `eval(arg)`. -/
def body (lit arg : Text) : Text :=
  "v=\"".toList ++ (lit ++ ('"' :: (";eval(".toList ++ (arg ++ [')']))))

def mk (lit arg : Text) : Text := PRE ++ (body lit arg ++ SUF)

def parseArg (x : Text) (r : Text) : Option (Text × Text) :=
  if r = ['v', ')'] then some (x, x)
  else match r with
    | c :: r => if c = '"' then
        match readLit r with
        | some (code, r') => if r' = [')'] then some (x, code) else none
        | none => none
      else none
    | [] => none

def parseBody (b : Text) : Option (Text × Text) :=
  match stripPrefix "v=\"".toList b with
  | some r =>
    match readLit r with
    | some (x, r) =>
      match stripPrefix ";eval(".toList r with
      | some r => parseArg x r
      | none => none
    | none => none
  | none => none

/-- Parse a file into the value of `v` and the code that is evaluated. -/
def parseFile (f : Text) : Option (Text × Text) :=
  match stripPrefix PRE f with
  | some r =>
    match stripSuffix SUF r with
    | some b => if (xmlRun 0 b).isSome then parseBody b else none
    | none => none
  | none => none

theorem xml_body (lit arg : Text) (hl : (xmlRun 0 lit).isSome)
    (ha : (xmlRun 0 (arg ++ [')'])).isSome) : (xmlRun 0 (body lit arg)).isSome := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hl
  have h1 : ∀ w, xmlRun 0 ("v=\"".toList ++ w) = xmlRun 0 w := fun w => by
    simp [xmlRun, xmlStep]
  have h2 : ∀ w, xmlRun 0 (";eval(".toList ++ w) = xmlRun 0 w := fun w => by
    simp [xmlRun, xmlStep]
  rw [body, h1, xmlRun_append, hs, Option.bind_some, xmlRun_quote, h2]
  exact ha

theorem parseFile_mk (lit arg x c : Text)
    (hl : ∀ r, readLit (lit ++ '"' :: r) = some (x, r)) (hxl : (xmlRun 0 lit).isSome)
    (ha : parseArg x (arg ++ [')']) = some (x, c)) (hxa : (xmlRun 0 (arg ++ [')'])).isSome) :
    parseFile (mk lit arg) = some (x, c) := by
  have hb := xml_body lit arg hxl hxa
  unfold parseFile mk
  rw [stripPrefix_append]
  dsimp only
  rw [stripSuffix_append]
  dsimp only
  rw [if_pos hb]
  unfold parseBody body
  rw [stripPrefix_append]
  dsimp only
  rw [hl]
  dsimp only
  rw [stripPrefix_append]
  exact ha

theorem parseArg_v (x : Text) : parseArg x (['v'] ++ [')']) = some (x, x) := by
  simp [parseArg]

theorem parseArg_lit (x c : Text) (hc : c.all rawOK = true) :
    parseArg x (('"' :: (c ++ ['"'])) ++ [')']) = some (x, c) := by
  simp [parseArg, readLit_raw [')'] c hc]

/-! ## The script fragment -/

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

/-- JavaScript source of an expression; string literals are template literals. -/
def Expr.show : Expr → Text
  | str s => '`' :: (s ++ ['`'])
  | var => ['v']
  | chr n => "H(".toList ++ ((toString n).toList ++ [')'])
  | add e₁ e₂ => e₁.show ++ ('+' :: e₂.show)

def readUntil (stop : Char) : Text → Option (Text × Text)
  | [] => none
  | c :: r =>
    if c = stop then some ([], r) else (readUntil stop r).map fun (s, r') => (c :: s, r')

def digitsVal (ds : Text) : Option Nat :=
  if ds ≠ [] ∧ ds.all Char.isDigit = true then
    some (ds.foldl (fun n d => 10 * n + (d.toNat - 48)) 0)
  else none

def parseAtom : Text → Option (Expr × Text)
  | [] => none
  | c :: r =>
    if c = '`' then
      match readUntil '`' r with
      | some (s, r') => if s.all (fun d => rawOK d && d != '$') then some (.str s, r') else none
      | none => none
    else if c = 'v' then some (.var, r)
    else if c = 'H' then
      match r with
      | '(' :: r =>
        match readUntil ')' r with
        | some (ds, r') => (digitsVal ds).map fun n => (.chr n, r')
        | none => none
      | _ => none
    else none

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

/-! ## The evaluated code, for a given library prefix -/

/-- The code `pre E)`, where `pre` is a library followed by `;f(` for its drawing function `f`. -/
def codeWith (pre : Text) (e : Expr) : Text := pre ++ (e.show ++ [')'])

/-- Parse evaluated code of the form `pre E)` into `E`. -/
def parseCodeWith (pre c : Text) : Option Expr :=
  match stripPrefix pre c with
  | some r =>
    match parseExpr r with
    | some (e, r') => if r' = [')'] then some e else none
    | none => none
  | none => none

/-- Texts that can be bound to `v` without escaping. -/
def safe (x : Text) : Bool := x.all rawOK && (xmlRun 0 x).isSome

/-- `sub c x` binds `x` to `v` and evaluates `c`; if `c = x` it evaluates `v` itself. -/
def sub (c x : Text) : Text := mk x (if c = x then ['v'] else '"' :: (c ++ ['"']))

theorem parseFile_sub {c x : Text} (hc : safe c = true) (hx : safe x = true) :
    parseFile (sub c x) = some (x, c) := by
  simp only [safe, Bool.and_eq_true] at hc hx
  unfold sub
  split
  · rename_i h
    subst h
    exact parseFile_mk _ _ _ _ (readLit_raw · c hx.1) hx.2 (parseArg_v c) (by decide)
  · refine parseFile_mk _ _ _ _ (readLit_raw · x hx.1) hx.2 (parseArg_lit x c hc.1) ?_
    obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hc.2
    rw [List.cons_append, xmlRun_quote, List.append_assoc, xmlRun_append, hs]
    simp [xmlRun, xmlStep]

/-! ## Quotation: a file that draws a given text -/

/-- The code `pre v)`: draw the value of `v`. -/
def showWith (pre : Text) : Text := codeWith pre .var

/-- A file that binds `t` (escaped) to `v` and draws it. -/
def quoteWith (pre t : Text) : Text := mk (esc t) ('"' :: (showWith pre ++ ['"']))

theorem parseFile_quoteWith (pre : Text) (hs : safe (showWith pre) = true) (t : Text)
    (ht : t.all (·.toNat < 256) = true) :
    parseFile (quoteWith pre t) = some (t, showWith pre) := by
  simp only [safe, Bool.and_eq_true] at hs
  refine parseFile_mk _ _ _ _ (readLit_esc · t ht) (xmlRun_esc t ht 0)
    (parseArg_lit t (showWith pre) hs.1) ?_
  obtain ⟨s, h⟩ := Option.isSome_iff_exists.1 hs.2
  rw [List.cons_append, xmlRun_quote, List.append_assoc, xmlRun_append, h]
  simp [xmlRun, xmlStep]

/-! ## The template -/

/-- `<svg xmlns='http://www.w3.org/2000/svg'><script>v="` ++ v ++ `";eval(v)</script></svg>`,
with `<` and `"` written as `H(60)` and `H(34)`. -/
def tmplExpr : Expr :=
  .add (.add (.add (.add (.add (.add (.add (.add (.add (.add (.add
    (.chr 60)
    (.str "svg xmlns='http://www.w3.org/2000/svg'>".toList))
    (.chr 60))
    (.str "script>v=".toList))
    (.chr 34))
    .var)
    (.chr 34))
    (.str ";eval(v)".toList))
    (.chr 60))
    (.str "/script>".toList))
    (.chr 60))
    (.str "/svg>".toList)

theorem eval_tmpl (x : Text) : tmplExpr.eval x = sub x x := by
  simp only [sub, if_pos, mk, body, PRE, SUF, tmplExpr, Expr.eval, List.append_assoc]
  rfl

theorem all256_of_safe {x : Text} (hx : safe x = true) : x.all (·.toNat < 256) = true := by
  simp only [safe, Bool.and_eq_true, List.all_eq_true] at hx
  simp only [List.all_eq_true, decide_eq_true_eq]
  intro c hc
  have := hx.1 c hc
  simp only [rawOK, Bool.and_eq_true, decide_eq_true_eq] at this
  omega

theorem all256_sub {x : Text} (hx : safe x = true) : (sub x x).all (·.toNat < 256) = true := by
  have h := all256_of_safe hx
  simp only [sub, if_pos, mk, body, List.all_append, List.all_cons, h]
  decide

end QuineEngine.SvgScript
