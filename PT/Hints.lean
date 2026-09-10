import Lean
import PT.Theorems
import PT.Predicate
import PT.Programs
import PT.Formula

open Lean Elab Tactic Meta

namespace PT

register_option pt.strict : Bool := {
  defValue := true
  descr := "PT: enforce the allowed command and tactic subset" }
register_option pt.sections : Nat := {
  defValue := 0
  descr := "PT: highest enabled appendix section; 0 enables all" }
register_option pt.check : Bool := {
  defValue := true
  descr := "PT: check proof steps" }
register_option pt.equalityOnly : Bool := {
  defValue := true
  descr := "PT: allow only equality steps in calculations" }
register_option pt.tests : Bool := {
  defValue := false
  descr := "PT: allow `#guard_msgs` and disable source scanning" }
register_option pt.assumed : String := {
  defValue := ""
  descr := "PT: internal assumption names for diagnostics" }

initialize appendixExt : EnvExtension (Option Nat) ← registerEnvExtension (pure none)

structure HintEntry where
  number : String
  name   : String
  group  : Name
  aliases : List String := []

def hintTable : List HintEntry := [
  ⟨"1.1",  "Commutativity", `Commutativity, []⟩,
  ⟨"1.2",  "Associativity", `Associativity, []⟩,
  ⟨"1.3",  "Distributivity", `Distributivity, []⟩,
  ⟨"",     "Distributivity of ∧ over ∨", `Distributivity.and, []⟩,
  ⟨"",     "Distributivity of ∨ over ∧", `Distributivity.or, []⟩,
  ⟨"1.4",  "De Morgan", `DeMorgan, ["DeMorgan"]⟩,
  ⟨"1.5",  "Negation", `Negation, ["Double Negation"]⟩,
  ⟨"1.6",  "Excluded Middle", `ExcludedMiddle, []⟩,
  ⟨"1.7",  "Contradiction", `Contradiction, []⟩,
  ⟨"1.8",  "Implication", `Implication, []⟩,
  ⟨"1.9",  "Equality", `Equality, []⟩,
  ⟨"1.10", "or-simplification", `OrSimplification, ["∨-simplification"]⟩,
  ⟨"1.11", "and-simplification", `AndSimplification, ["∧-simplification"]⟩,
  ⟨"1.12", "Identity", `Identity, []⟩,
  ⟨"2.1",  "Associativity of =", `AssociativityOfEq, []⟩,
  ⟨"2.2",  "Identity of =", `IdentityOfEq, []⟩,
  ⟨"2.3",  "Truth", `Truth, []⟩,
  ⟨"2.4",  "Definition of F", `DefinitionOfF, []⟩,
  ⟨"2.5",  "Distributivity of ¬ over =", `DistributivityOfNotOverEq, []⟩,
  ⟨"2.6",  "Negation of F", `NegationOfF, []⟩,
  ⟨"2.7",  "Definition of ¬", `DefinitionOfNot, []⟩,
  ⟨"2.8",  "Distributivity of ∨ over =", `DistributivityOfOrOverEq, []⟩,
  ⟨"2.9",  "Distributivity of ∨ over ∨", `DistributivityOfOrOverOr, []⟩,
  ⟨"2.10", "Mutual definition of ∧ and ∨", `MutualDefinition, ["Mutual definition"]⟩,
  ⟨"2.11", "Distributivity of ∧ over ∧", `DistributivityOfAndOverAnd, []⟩,
  ⟨"2.12", "Absorption", `Absorption, []⟩,
  ⟨"2.13", "Distributivity of ∧ over =", `DistributivityOfAndOverEq, []⟩,
  ⟨"2.14", "Replacement", `Replacement, []⟩,
  ⟨"2.15", "Definition of =", `DefinitionOfEq, []⟩,
  ⟨"2.16", "Exclusive or", `ExclusiveOr, ["xor"]⟩,
  ⟨"2.17", "Definition of Implication", `DefinitionOfImplication, ["Definition of ⇒"]⟩,
  ⟨"2.18", "Contrapositive", `Contrapositive, []⟩,
  ⟨"2.19", "Distributivity of ⇒ over =", `DistributivityOfImpOverEq, []⟩,
  ⟨"2.20", "Shunting", `Shunting, []⟩,
  ⟨"2.21", "Elimination/Introduction of ⇒", `EliminationIntroduction,
           ["Elimination of ⇒", "Introduction of ⇒", "Elimination/Introduction"]⟩,
  ⟨"2.22", "Right Zero of ⇒", `RightZeroOfImp, []⟩,
  ⟨"2.23", "Left Identity of ⇒", `LeftIdentityOfImp, []⟩,
  ⟨"2.24", "Weakening/Strengthening", `Weakening, ["Weakening", "Strengthening"]⟩,
  ⟨"2.25", "Modus Ponens", `ModusPonens, []⟩,
  ⟨"2.26", "Proof by Cases", `ProofByCases, []⟩,
  ⟨"2.27", "Mutual Implication", `MutualImplication, []⟩,
  ⟨"2.28", "Antisymmetry", `Antisymmetry, []⟩,
  ⟨"2.29", "Transitivity", `Transitivity, []⟩,
  ⟨"2.30", "Monotonicity of ∨", `MonotonicityOfOr, []⟩,
  ⟨"2.31", "Monotonicity of ∧", `MonotonicityOfAnd, []⟩,
  ⟨"2.32", "Leibniz", `Leibniz, []⟩,
  ⟨"2.33", "Substitution", `Substitution, ["Arithmetic Substitution"]⟩,
  ⟨"2.34", "Replace by T", `ReplaceByT, ["Replace by true"]⟩,
  ⟨"2.35", "Replace by F", `ReplaceByF, ["Replace by false"]⟩,
  ⟨"2.36", "Shannon", `Shannon, []⟩,
  ⟨"3.1",  "Definition of ∃", `DefinitionOfExists, ["Definition of exists"]⟩,
  ⟨"3.2",  "Definition of ∀", `DefinitionOfForall, ["Definition of forall"]⟩,
  ⟨"3.3",  "Range Split", `RangeSplit, []⟩,
  ⟨"3.4",  "Interchange of Dummies", `InterchangeOfDummies, []⟩,
  ⟨"3.5",  "Dummy Renaming", `DummyRenaming, []⟩,
  ⟨"3.6",  "Distributivity of ∨ over ∀", `DistributivityOfOrOverForall, ["Distributivity of or over forall"]⟩,
  ⟨"3.7",  "Distributivity of ∧ over ∀", `DistributivityOfAndOverForall, ["Distributivity of and over forall"]⟩,
  ⟨"3.8",  "Distributivity of ∧ over ∃", `DistributivityOfAndOverExists, ["Distributivity of and over exists"]⟩,
  ⟨"3.9",  "Distributivity of ∨ over ∃", `DistributivityOfOrOverExists, ["Distributivity of or over exists"]⟩,
  ⟨"3.10", "Universality of T", `UniversalityOfT, []⟩,
  ⟨"3.11", "Existence of F", `ExistenceOfF, []⟩,
  ⟨"3.12", "Generalized De Morgan", `GeneralizedDeMorgan, ["Generalised De Morgan"]⟩,
  ⟨"3.13", "Trading", `Trading, []⟩,
  ⟨"3.14", "Definition of N", `DefinitionOfCount, ["Definition of Numerical Quantification"]⟩,
  ⟨"3.15", "Definition of Σ", `DefinitionOfSum, ["Definition of Sum"]⟩,
  ⟨"3.16", "Definition of Π", `DefinitionOfProduct, ["Definition of Product"]⟩,
  ⟨"",     "Generalized Definition of ∀", `GeneralizedDefinitionOfForall,
           ["Generalised Definition of ∀", "Generalized Definition of forall"]⟩,
  ⟨"",     "Generalized Definition of ∃", `GeneralizedDefinitionOfExists,
           ["Generalised Definition of ∃", "Generalized Definition of exists"]⟩,
  ⟨"5.1",  "Assignment to Array Element", `AssignmentToArrayElement, []⟩,
  ⟨"5.2",  "Definition of Arithmetic Relations", `DefinitionOfArithmeticRelations,
           ["Definition of <", "Definition of >", "Definition of ≤",
            "Definition of ≥", "Definition of ≠", "Definition of ∈"]⟩,
  ⟨"6.1",  "Law of Excluded Miracle", `ExcludedMiracle, ["Excluded Miracle"]⟩,
  ⟨"6.2",  "Distributivity of Conjunction", `DistributivityOfConjunction, []⟩,
  ⟨"6.3",  "Law of Monotonicity", `Monotonicity, ["Monotonicity"]⟩,
  ⟨"6.4",  "Distributivity of Disjunction", `DistributivityOfDisjunction, []⟩,
  ⟨"7.1",  "Definition of skip", `DefinitionOfSkip, []⟩,
  ⟨"8.1",  "Definition of abort", `DefinitionOfAbort, []⟩,
  ⟨"9.1",  "Definition of Sequential Composition", `DefinitionOfSequentialComposition,
           ["Sequential Composition"]⟩,
  ⟨"10.1", "Definition of Assignment", `DefinitionOfAssignment, ["Assignment", "10.2",
           "Definition of Multiple Assignment", "Definition of Multiple Assignments",
           "Multiple Assignment", "Definition of simultaneous assignment"]⟩,
  ⟨"11.2", "Definition of IF", `DefinitionOfIF, ["11.1", "Definition of the alternative command",
           "Alternative Command", "Definition of the alternative command IF"]⟩ ]

/-- Ignore case, spaces, and hyphens in hint names. -/
def normalizeHint (s : String) : String :=
  let s := s.trimAscii.toString.toLower
  String.ofList (s.toList.filter fun c =>
    !(c == ' ' || c == '-' || c == '_' || c == '/' || c == '\'' || c == '\t' || c == '\n' || c == '\r'))

def isAssumptionKey (k : String) : Bool :=
  ["assumption", "assumptions", "hypothesis", "hypotheses", "premise", "premises"].contains k

/-- Levenshtein distance, used to suggest a close name. -/
def editDistance (a b : String) : Nat := Id.run do
  let a := a.toList.toArray
  let b := b.toList.toArray
  let mut prev : Array Nat := Array.range (b.size + 1)
  for i in [0:a.size] do
    let mut cur : Array Nat := #[i + 1]
    for j in [0:b.size] do
      let cost := if a[i]! == b[j]! then 0 else 1
      let v := min (min (prev[j+1]! + 1) (cur[j]! + 1)) (prev[j]! + cost)
      cur := cur.push v
    prev := cur
  return prev[b.size]!

def nearest (k : String) (n : Nat) : List String :=
  let names := hintTable.map (·.name)
  let scored := names.map fun nm => (editDistance k (normalizeHint nm), nm)
  (scored.toArray.qsort (fun a b => a.1 < b.1)).toList.take n |>.map (·.2)

def suggestions (k : String) : List String :=
  let names := hintTable.map (·.name) ++ hintTable.foldl (fun acc e => acc ++ e.aliases) []
  let scored := names.filterMap fun n =>
    let d := editDistance (normalizeHint n) k
    if d ≤ 3 && d * 3 ≤ k.length + 2 then some (d, n) else none
  (scored.toArray.qsort (fun a b => a.1 < b.1)).toList.map (·.2) |>.eraseDups |>.take 3

private def lawModules : List Name := [`PT.Axioms, `PT.Theorems, `PT.Predicate, `PT.Programs]

def allLaws (env : Environment) : Array Name := Id.run do
  let mut out := #[]
  for m in lawModules do
    if let some idx := env.getModuleIdx? m then
      for c in env.header.moduleData[idx]!.constNames do
        if c.isInternal || c.isInternalDetail then continue
        if (env.find? c).any (·.isTheorem) then out := out.push c
  return out.qsort (fun a b => a.toString < b.toString)

/-- Theorems named `PT.g` or `PT.g.*`, the lines of an appendix entry. -/
def expandGroup (env : Environment) (g : Name) : Array Name :=
  if g.isAnonymous then #[] else
  let full := `PT ++ g
  (allLaws env).filter fun c => c == full || full.isPrefixOf c

inductive LawKind | equiv | imp | schema | other
  deriving BEq, Repr

def stripForall : Expr → Expr
  | .forallE _ _ b _ => stripForall b
  | e => e

def isContextType (d : Expr) : Bool :=
  d.isArrow && (d.bindingDomain!.isProp || d.bindingDomain!.isConstOf ``Int) && d.bindingBody!.isProp

/-- Context arguments, or `none` for an unapplied context or a bound argument. -/
private partial def contextUses (e : Expr) (k0 ℓ : Nat) : Option (Array Expr) :=
  match e with
  | .app f a =>
    if f == .bvar (k0 + ℓ) then
      match a with
      | .bvar j => if j < ℓ then none else some #[a]
      | _ => do return (← contextUses a k0 ℓ).push a
    else do return (← contextUses f k0 ℓ) ++ (← contextUses a k0 ℓ)
  | .bvar k => if k == k0 + ℓ then none else some #[]
  | .lam _ d b _ => do return (← contextUses d k0 ℓ) ++ (← contextUses b k0 (ℓ + 1))
  | .forallE _ d b _ => do return (← contextUses d k0 ℓ) ++ (← contextUses b k0 (ℓ + 1))
  | .letE _ t v b _ => do
    return (← contextUses t k0 ℓ) ++ (← contextUses v k0 ℓ) ++ (← contextUses b k0 (ℓ + 1))
  | .mdata _ b => contextUses b k0 ℓ
  | _ => some #[]

private def hasContextArg (ty : Expr) : Bool := Id.run do
  let mut binders : Array Expr := #[]
  let mut body := ty
  while body.isForall do
    binders := binders.push body.bindingDomain!
    body := body.bindingBody!
  let n := binders.size
  for d in binders, i in [0:n] do
    if isContextType d then
      if let some uses := contextUses body (n - 1 - i) 0 then
        if (uses.foldl (fun acc u => if acc.contains u then acc else acc.push u) #[]).size ≥ 2 then
          return true
  return false

def classifyType (ty : Expr) : LawKind :=
  let body := stripForall ty
  if hasContextArg ty then .schema
  else if body.isAppOfArity ``Iff 2 || body.isAppOfArity ``Eq 3 then .equiv
  else if body.isAppOfArity ``PT.Imp 2 then .imp
  else .other

def classify (env : Environment) (c : Name) : LawKind :=
  match env.find? c with
  | none => .other
  | some ci => classifyType ci.type

def isUserDecl (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => true
  | some idx => !([`Init, `Lean, `Std, `Lake, `PT].contains (env.header.moduleNames[idx]!.getRoot))

def sectionOf (e : HintEntry) : Nat :=
  if e.number == "" then (if e.name.startsWith "Distributivity" then 1 else 3)
  else (e.number.takeWhile (· != '.')).toNat?.getD 0

def inSections (maxSec : Nat) (e : HintEntry) : Bool := maxSec == 0 || sectionOf e ≤ maxSec

def hintEntries (s : String) : List HintEntry :=
  let k := normalizeHint s
  hintTable.filter fun e =>
    (e.number != "" && normalizeHint e.number == k) || normalizeHint e.name == k ||
    e.aliases.any (normalizeHint · == k)

/-- Resolve appendix entries or proof blocks visible in the current namespace. -/
def lookupHint (env : Environment) (s : String) (maxSec : Nat := 0) (ns : Name := .anonymous) : Array Name :=
  let hits := (hintEntries s).filter (inSections maxSec)
  let byTable := hits.foldl (fun acc e => acc ++ expandGroup env e.group) #[]
  if !byTable.isEmpty then byTable
  else
    let t := s.trimAscii.toString
    if t.any (fun c => c == ' ' || c == '-' || c == '/' || c == ':') then #[]
    else
      let n := t.toName
      if n.isAnonymous then #[]
      else

        let n := if env.contains n then n else ns ++ n
        match env.find? n with
          | some ci =>
            if isUserDecl env n && ci.isTheorem && proofTag.hasTag env n then #[n] else #[]
          | none => #[]

def unknownHint (env : Environment) (item : String) (maxSec : Nat) : MessageData :=
  let k := normalizeHint item
  if let some e := (hintEntries item).head? then
    if e.number == "" then
      m!"`{item}` is in section {sectionOf e} of the appendix, outside the enabled sections 1-{maxSec}"
    else
      m!"`{item}` is theorem {e.number} of the appendix, outside the enabled sections 1-{maxSec}"
  else
    let n := item.trimAscii.toString.toName
    if (env.find? n).isSome && !isUserDecl env n then
      m!"`{item}` is a Lean name, cite a theorem by its name in the appendix"
    else if (env.find? n).isSome && !proofTag.hasTag env n then
      m!"`{item}` is not written as a proof block, so it cannot be cited"
    else if k.startsWith "assumption" || k.startsWith "hypothes" || k.startsWith "premise" then
      m!"`{item}` is not an assumption hint. An assumption is cited by its formula, `Assumption: p`"
    else
      let sug := suggestions k
      if sug.isEmpty then
        m!"`{item}` is not an axiom or theorem of the appendix. Close names are {", ".intercalate (nearest k 5)}"
      else
        m!"`{item}` is not an axiom or theorem of the appendix. Did you mean {", ".intercalate (sug.map (s!"`{·}`"))}?"

/-- Split items at commas outside brackets. A colon selects a formula. -/
def parseHint (s : String) : List (String × Option String) := Id.run do
  let mut items : Array String := #[]
  let mut cur := ""
  let mut depth := 0
  for c in s.toList do
    if c == '(' || c == '[' || c == '{' then depth := depth + 1
    if c == ')' || c == ']' || c == '}' then depth := depth - 1
    if c == ',' && depth == 0 then items := items.push cur; cur := ""
    else cur := cur.push c
  items := items.push cur
  items.toList.map (·.trimAscii.toString) |>.filter (· ≠ "") |>.map fun item =>
    match item.splitOn ":" with
    | h :: rest =>
      if rest.isEmpty then (item, none)
      else (h.trimAscii.toString, some ((":".intercalate rest).trimAscii.toString))
    | [] => (item, none)

def indexOf (s sub : String) : Option Nat := Id.run do
  let cs := s.toList
  let sc := sub.toList
  let mut off := 0
  for i in [0:cs.length] do
    if (cs.drop i).take sc.length == sc then return some off
    off := off + (cs[i]!).utf8Size
  return none

def addHintInfo (hintStx : Syntax) (hintText item : String) (n : Name) : TacticM Unit := do
  let some pos := hintStx.getPos? | return
  let some off := indexOf hintText item | return
  let a : String.Pos.Raw := ⟨pos.byteIdx + off⟩
  let b : String.Pos.Raw := ⟨pos.byteIdx + off + item.utf8ByteSize⟩
  addConstInfo (Syntax.atom (.synthetic a b true) item) n

/-- Hint-local offsets must not become editor positions in the source file. -/
partial def noPositions : Syntax → Syntax
  | .node _ k args => .node .none k (args.map noPositions)
  | .atom _ v => .atom .none v
  | .ident _ raw v pre => .ident .none raw v pre
  | s => s

def elabHintFormula (text : String) : TacticM (Option Expr) := do
  let text := text.trimAscii.toString
  if text.isEmpty then return none
  match Parser.runParserCategory (← getEnv) `ptf text with
  | .error _ => return none
  | .ok stx =>
    let stx := noPositions stx
    try
      let t ← `(⟪$(⟨stx⟩):ptf⟫)
      let e ← Term.withoutErrToSorry <| Tactic.elabTerm t none
      Term.synthesizeSyntheticMVarsNoPostponing
      return some (← instantiateMVars e)
    catch _ => return none

end PT
