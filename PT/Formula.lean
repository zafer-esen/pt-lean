import Lean
import PT.Core
import PT.Quantifiers
import PT.Programs
/-! Formula and command syntax. Formula equality is `↔` and integer equality is `=`. -/

open Lean Elab Term Meta

namespace PT

declare_syntax_cat ptf (behavior := both)
syntax:max ident : ptf
syntax:max num : ptf
syntax "(" ptf ")" : ptf

syntax:max (name := ptApp) ident noWs "(" ptf,+ ")" : ptf

syntax:75 "-" ptf:75 : ptf
syntax:80 ptf:81 " ^ " num : ptf
syntax:70 ptf:70 " * " ptf:71 : ptf
syntax:70 ptf:70 " / " ptf:71 : ptf
syntax:70 (name := ptMod) ptf:70 " mod " ptf:71 : ptf
syntax:65 ptf:65 " + " ptf:66 : ptf
syntax:65 ptf:65 " - " ptf:66 : ptf

syntax:50 ptf:51 " < " ptf:51 : ptf
syntax:50 (name := ptLe) ptf:51 " ≤ " ptf:51 : ptf
syntax:50 ptf:51 " > " ptf:51 : ptf
syntax:50 (name := ptGe) ptf:51 " ≥ " ptf:51 : ptf
syntax:50 (name := ptNe) ptf:51 " ≠ " ptf:51 : ptf
syntax:50 ptf:51 " ≤ " ptf:51 " < " ptf:51 : ptf
syntax:50 ptf:51 " ≤ " ptf:51 " ≤ " ptf:51 : ptf
syntax:50 ptf:51 " < " ptf:51 " < " ptf:51 : ptf
syntax:50 ptf:51 " < " ptf:51 " ≤ " ptf:51 : ptf

syntax:max (name := ptNot) "¬" ptf:40 : ptf
syntax:35 (name := ptAnd) ptf:36 " ∧ " ptf:35 : ptf
syntax:30 (name := ptOr) ptf:31 " ∨ " ptf:30 : ptf
syntax:25 (name := ptImp) ptf:26 atomic(" ⇒ " ptf:25) : ptf
syntax:20 (name := ptEq) ptf:21 atomic(" = " ptf:20) : ptf

syntax:max (name := ptIndex) ptf:max noWs atomic("[" ptf "]") : ptf
syntax:max (name := ptUpd) "(" ptf "; " ptf " : " ptf ")" : ptf
syntax:50 (name := ptSecEq) ptf:max noWs "[" ptf " : " ptf "]" " = " ptf:51 : ptf
syntax:50 (name := ptSecLt) ptf:max noWs "[" ptf " : " ptf "]" " < " ptf:51 : ptf
syntax:50 (name := ptSecGt) ptf:max noWs "[" ptf " : " ptf "]" " > " ptf:51 : ptf
syntax:50 (name := ptSecLe) ptf:max noWs "[" ptf " : " ptf "]" " ≤ " ptf:51 : ptf
syntax:50 (name := ptSecGe) ptf:max noWs "[" ptf " : " ptf "]" " ≥ " ptf:51 : ptf
syntax:50 (name := ptSecNe) ptf:max noWs "[" ptf " : " ptf "]" " ≠ " ptf:51 : ptf
syntax:50 (name := ptSecMem) ptf:51 " ∈ " ptf:max noWs "[" ptf " : " ptf "]" : ptf

declare_syntax_cat ptcmd (behavior := both)
syntax &"skip" : ptcmd
syntax &"abort" : ptcmd
syntax ident : ptcmd
syntax (name := ptAssignCmd) atomic(ident,+ " := ") ptf,+ : ptcmd
syntax ident noWs "[" ptf "]" " := " ptf : ptcmd
syntax:10 ptcmd:11 "; " ptcmd:10 : ptcmd
syntax "(" ptcmd ")" : ptcmd
syntax ptGuard := ptf " → " ptcmd
syntax (name := ptIf) "if " sepBy1(ptGuard, " □ ") &"fi" : ptcmd
syntax (name := ptIfBar) "if " sepBy1(ptGuard, " | ") &"fi" : ptcmd
-- Assignment values and the postcondition share commas. `wpSplit` separates them.

syntax:max (name := ptWp) "wp" noWs "(" ptcmd (", " ptf)? ")" : ptf

syntax:max (name := ptWpStr) "wp" noWs "(" str ", " ptf ")" : ptf
syntax:max (name := ptWpQuote) "wp" noWs "(" "“" ptcmd "”" ", " ptf ")" : ptf

syntax:25 (name := ptImpA) ptf:26 atomic(" => " ptf:25) : ptf
syntax:25 (name := ptImpB) ptf:26 atomic(" -> " ptf:25) : ptf
syntax:50 (name := ptLeA) ptf:51 " <= " ptf:51 : ptf
syntax:50 (name := ptGeA) ptf:51 " >= " ptf:51 : ptf
syntax:50 (name := ptNeA) ptf:51 " != " ptf:51 : ptf
syntax:70 (name := ptModA) ptf:70 " % " ptf:71 : ptf
syntax:35 (name := ptAndA) ptf:36 " /\\ " ptf:35 : ptf
syntax:30 (name := ptOrA) ptf:31 " \\/ " ptf:30 : ptf
syntax:max (name := ptNotA) "~" ptf:40 : ptf
syntax (name := ptForallA) "forall " ident " : " ptf " : " ptf : ptf
syntax (name := ptExistsA) "exists " ident " : " ptf " : " ptf : ptf

syntax (name := ptForall) "∀ " ident " : " ptf " : " ptf : ptf
syntax (name := ptExists) "∃ " ident " : " ptf " : " ptf : ptf
syntax "Σ " ident " : " ptf:51 " ≤ " ident " < " ptf:51 " : " ptf : ptf
syntax "Π " ident " : " ptf:51 " ≤ " ident " < " ptf:51 " : " ptf : ptf
syntax &"N" ppSpace ident " : " ptf:51 " ≤ " ident " < " ptf:51 " : " ptf : ptf

/-- Normalize ASCII spellings -/
partial def canon : Syntax → Syntax
  | .node info k args =>
    let args := args.map canon
    let sym (k' : SyntaxNodeKind) (old new : String) : Syntax :=
      .node info k' (args.map fun a => match a with
        | .atom i v => if v.trimAscii.toString == old then .atom i new else a
        | _ => a)
    if k == ``ptImpA then sym ``ptImp "=>" "⇒"
    else if k == ``ptImpB then sym ``ptImp "->" "⇒"
    else if k == ``ptLeA then sym ``ptLe "<=" "≤"
    else if k == ``ptGeA then sym ``ptGe ">=" "≥"
    else if k == ``ptNeA then sym ``ptNe "!=" "≠"
    else if k == ``ptModA then sym ``ptMod "%" "mod"
    else if k == ``ptAndA then sym ``ptAnd "/\\" "∧"
    else if k == ``ptOrA then sym ``ptOr "\\/" "∨"
    else if k == ``ptNotA then sym ``ptNot "~" "¬"
    else if k == ``ptForallA then sym ``ptForall "forall" "∀"
    else if k == ``ptExistsA then sym ``ptExists "exists" "∃"
    else .node info k args
  | s => s

syntax "⟪" ptf "⟫" : term

/-! `=` normally has lowest precedence, but not for integer `=`
e.g. `x = y ∧ P` becomes `(x = y) ∧ P`. -/

private def connective? (f : Syntax) : Option (Syntax × Syntax × Syntax × Syntax) :=
  if f.getNumArgs == 3 && f[1].isAtom && ["∧", "∨", "⇒", "="].contains f[1].getAtomVal then
    some (f[0], f[1], f[2], f)
  else none

private partial def replaceLeftmost (f : Syntax) (g : Syntax → MacroM Syntax) : MacroM Syntax := do
  match connective? f with
  | some (l, _, _, _) => return f.setArg 0 (← replaceLeftmost l g)
  | none => g f

private partial def replaceRightmost (f : Syntax) (g : Syntax → MacroM Syntax) : MacroM Syntax := do
  match connective? f with
  | some (_, _, r, _) => return f.setArg 2 (← replaceRightmost r g)
  | none =>
    if f.getNumArgs == 2 && f[0].isAtom && f[0].getAtomVal == "¬" then
      return f.setArg 1 (← replaceRightmost f[1] g)
    else g f
private partial def leftmost (f : Syntax) : Syntax :=
  match connective? f with | some (l, _, _, _) => leftmost l | none => f
private partial def rightmost (f : Syntax) : Syntax :=
  match connective? f with
  | some (_, _, r, _) => rightmost r
  | none => if f.getNumArgs == 2 && f[0].isAtom && f[0].getAtomVal == "¬" then rightmost f[1] else f

private def elabsToInt (f : Syntax) : TermElabM Bool := do
  let s ← saveState
  try
    let e ← withoutErrToSorry <| elabTerm (← `(⟪$(⟨f⟩):ptf⟫)) none
    synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars (← inferType e)
    s.restore
    return ty.isConstOf ``Int
  catch _ => s.restore; return false

syntax (name := ptStepTerm) "pt_step% " ptf ptf : term
@[term_elab ptStepTerm] def elabPtStep : TermElab := fun stx _ => do
  let a ← elabTerm (← `(⟪$(⟨stx[1]⟩):ptf⟫)) none
  synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars (← inferType a)
  let b ← elabTermEnsuringType (← `(⟪$(⟨stx[2]⟩):ptf⟫)) ty
  if ty.isProp then return mkApp2 (mkConst ``Iff) a b
  else mkEq a b

private def mkEqStx (a b : Syntax) : MacroM Syntax := do
  let a : TSyntax `ptf := ⟨a⟩
  let b : TSyntax `ptf := ⟨b⟩
  return (← `(ptf| ($a = $b)))

/-- Reassociate integer equations after the variables are in scope. -/
partial def reassoc (f : Syntax) : TermElabM Syntax := do
  let f := canon f
  let f := f.setArgs (← f.getArgs.mapM reassoc)
  unless f.getKind == ``ptEq do return f
  let l := f[0]
  let r := f[2]
  let isNeg (l : Syntax) := l.getNumArgs == 2 && l[0].isAtom && l[0].getAtomVal == "¬"
  if ← elabsToInt l then
    if (connective? r).isSome && (← elabsToInt (leftmost r)) then
      return ← liftMacroM <| replaceLeftmost r fun c => mkEqStx l c
  else if (connective? l).isSome || isNeg l then
    if (← elabsToInt (rightmost l)) && (← elabsToInt (leftmost r)) then
      return ← liftMacroM <| replaceLeftmost r fun c => replaceRightmost l fun b => mkEqStx b c
    else if ← elabsToInt (rightmost l) then
      return ← liftMacroM <| replaceRightmost l fun b => mkEqStx b r
  return f

syntax (name := ptEqTerm) "pt_eq% " ptf ptf : term
@[term_elab ptEqTerm] def elabPtEq : TermElab := fun stx expectedType? => do
  let f ← reassoc (← `(ptf| $(⟨stx[1]⟩):ptf = $(⟨stx[2]⟩):ptf))
  unless f.getKind == ``ptEq do
    return ← elabTerm (← `(⟪$(⟨f⟩):ptf⟫)) expectedType?
  let a ← elabTerm (← `(⟪$(⟨f[0]⟩):ptf⟫)) none
  synthesizeSyntheticMVarsNoPostponing
  let ty ← instantiateMVars (← inferType a)
  let b ← elabTermEnsuringType (← `(⟪$(⟨f[2]⟩):ptf⟫)) ty
  if ty.isProp then return mkApp2 (mkConst ``Iff) a b
  else mkEq a b

syntax (name := ptTrans) "pt_trans% " term:max term:max : term
@[term_elab ptTrans] def elabPtTrans : TermElab := fun stx _ => do
  let h₁ ← elabTerm stx[1] none
  let h₂ ← elabTerm stx[2] none
  let kind (t : Expr) : Name :=
    if t.isAppOfArity ``Iff 2 then `iff else if t.isAppOfArity ``Eq 3 then `eq
    else if t.isAppOfArity ``PT.Imp 2 then `imp else `other
  let t₁ ← instantiateMVars (← inferType h₁)
  let t₂ ← instantiateMVars (← inferType h₂)
  match kind t₁, kind t₂ with
  | `iff, `iff => mkAppM ``Iff.trans #[h₁, h₂]
  | `eq, `eq => mkAppM ``Eq.trans #[h₁, h₂]
  | `iff, `imp => mkAppM ``PT.step_ei #[h₁, h₂]
  | `imp, `iff => mkAppM ``PT.step_ie #[h₁, h₂]
  | `imp, `imp => mkAppM ``PT.step_ii #[h₁, h₂]
  | _, _ => throwError "cannot chain{indentExpr t₁}\nwith{indentExpr t₂}"

def stateName? : TermElabM (Option Name) := do
  try pure (some (← realizeGlobalConstNoOverload (mkIdent `St))) catch _ => pure none

/-- State fields become `σ.x`. Predicates and bound functions become `P σ`. -/
syntax (name := ptVar) "pt_var% " ident : term
@[term_elab ptVar] def elabPtVar : TermElab := fun stx expectedType? => do
  let x : Ident := ⟨stx[1]⟩
  let σ := mkIdent `σ
  let lctx ← getLCtx
  let plain := elabTerm x expectedType?
  let some σd := lctx.findFromUserName? `σ | plain
  if let some d := lctx.findFromUserName? x.getId then
    let ty ← whnfR d.type
    let σty ← instantiateMVars σd.type
    if ty.isArrow && !σty.hasMVar then
      if ← isDefEq ty.bindingDomain! σty then elabTerm (← `($x $σ)) expectedType?
      else plain
    else plain
  else if let some st ← stateName? then
    if (← getEnv).contains (st ++ x.getId) then
      elabTerm (← `($(mkIdent (st ++ x.getId)) $σ)) expectedType?
    else plain
  else plain

syntax (name := ptAssign) "pt_assign% " "[" ident,* "]" "[" term,* "]" : term
@[term_elab ptAssign] def elabPtAssign : TermElab := fun stx _ => do
  let xs := stx[2].getSepArgs.map (·.getId)
  let es := stx[5].getSepArgs
  let some st ← stateName? | throwError "no program variables: declare them with `state x y : Int`"
  let some info := getStructureInfo? (← getEnv) st
    | throwError "no program variables: declare them with `state x y : Int`"
  for x in xs do
    unless info.fieldNames.contains x do throwError "`{x}` is not a program variable (declare it in `state`)"
  for x in xs, i in [0:xs.size] do
    if (xs.extract 0 i).contains x then throwError "`{x}` is assigned twice in one assignment"
  unless xs.size == es.size do
    throwError "the assignment has {xs.size} variable{if xs.size == 1 then "" else "s"} on the left and {es.size} expression{if es.size == 1 then "" else "s"} on the right"
  let σ := mkIdent `σ
  let mut args : Array Term := #[]
  for f in info.fieldNames do
    match xs.idxOf? f with
    | some k => args := args.push ⟨es[k]!⟩
    | none => args := args.push (← `($(mkIdent (st ++ f)) $σ))
  elabTerm (← `(fun ($σ : $(mkIdent `St)) => $(mkIdent (st ++ `mk)) $args*)) none

/-- Recover the postcondition parsed as an assignment value. -/
partial def wpSplit (S : Syntax) : Option (Syntax × Syntax) :=
  if S.getKind == ``ptAssignCmd then
    let xs := S[0].getSepArgs
    let es := S[2].getSepArgs
    if es.size == xs.size + 1 then
      let es' := S[2].getArgs.extract 0 (S[2].getArgs.size - 2)
      some (S.setArg 2 (S[2].setArgs es'), es.back!)
    else none
  else if S.getKind == ``PT.«ptcmd_;_» then
    (wpSplit S[2]).map fun (S₂, R) => (S.setArg 2 S₂, R)
  else none

def sameDummy (i j : Ident) : MacroM Unit := do
  unless i.getId == j.getId do
    Macro.throwErrorAt j s!"the dummy is `{i.getId}`, so the range is written `… ≤ {i.getId} < …`, not with `{j.getId}`"

macro_rules
  | `(⟪ Σ $i:ident : $m:ptf ≤ $j:ident < $n:ptf : $e:ptf ⟫) => do
    sameDummy i j; `(PT.Summation ⟪$m⟫ ⟪$n⟫ (fun ($i : Int) => ⟪$e⟫))
  | `(⟪ Π $i:ident : $m:ptf ≤ $j:ident < $n:ptf : $e:ptf ⟫) => do
    sameDummy i j; `(PT.Product ⟪$m⟫ ⟪$n⟫ (fun ($i : Int) => ⟪$e⟫))
  | `(⟪ N $i:ident : $m:ptf ≤ $j:ident < $n:ptf : $p:ptf ⟫) => do
    sameDummy i j; `(PT.Count ⟪$m⟫ ⟪$n⟫ (fun ($i : Int) => ⟪$p⟫))

syntax (name := ptWpStrTerm) "pt_wpstr% " str ptf : term
@[term_elab ptWpStrTerm] def elabPtWpStr : TermElab := fun stx expectedType? => do
  let some text := stx[1].isStrLit? | throwError "expected a string"
  match Parser.runParserCategory (← getEnv) `ptcmd text with
  | .error e => throwErrorAt stx[1] "not a command: {e}"
  | .ok cmd => elabTerm (← `(⟪ wp($(⟨cmd⟩):ptcmd, $(⟨stx[2]⟩):ptf) ⟫)) expectedType?

syntax "⟦" ptcmd "⟧" : term
macro_rules
  | `(⟦ skip ⟧) => `(PT.Cmd.skip)
  | `(⟦ abort ⟧) => `(PT.Cmd.abort)
  | `(⟦ $S:ident ⟧) => `($S)
  | `(⟦ $xs:ident,* := $es:ptf,* ⟧) => do
    let es ← es.getElems.mapM fun e => `(⟪$e⟫)
    `(PT.Cmd.assign (pt_assign% [$xs,*] [$es,*]))
  | `(⟦ $b:ident[$i:ptf] := $e:ptf ⟧) =>
    `(PT.Cmd.assign (pt_assign% [$b] [PT.upd ⟪$b:ident⟫ ⟪$i⟫ ⟪$e⟫]))
  | `(⟦ $S₁:ptcmd; $S₂:ptcmd ⟧) => `(PT.Cmd.seq ⟦$S₁⟧ ⟦$S₂⟧)
  | `(⟦ ($S:ptcmd) ⟧) => `(⟦$S⟧)
  | `(⟦ $c:ptcmd ⟧) => do
    unless c.raw.getKind == ``ptIf || c.raw.getKind == ``ptIfBar do Macro.throwUnsupported
    let σ := mkIdent `σ
    let branches ← c.raw[1].getSepArgs.mapM fun g => do
      let B : TSyntax `ptf := ⟨g[0]⟩
      let S : TSyntax `ptcmd := ⟨g[2]⟩
      `(((fun ($σ : $(mkIdent `St)) => ⟪$B⟫), ⟦$S⟧))
    `(PT.Cmd.ifc [$branches,*])

macro_rules
  | `(⟪ $x:ident ⟫) =>
    let n := x.getId
    if n == `T || n == `true || n == `True then `(PT.T)
    else if n == `F || n == `false || n == `False then `(PT.F)
    else `(pt_var% $x)
  | `(⟪ wp($S:ptcmd, $R:ptf) ⟫) => do
    let σ := mkIdent `σ
    `(PT.wp ⟦$S⟧ (fun ($σ : $(mkIdent `St)) => ⟪$R⟫) $σ)
  | `(⟪ wp(“$S:ptcmd”, $R:ptf) ⟫) => `(⟪ wp($S:ptcmd, $R:ptf) ⟫)
  | `(⟪ wp($s:str, $R:ptf) ⟫) => `(pt_wpstr% $s $R)
  | `(⟪ $a:ptf => $b:ptf ⟫) => `(⟪ $a ⇒ $b ⟫)
  | `(⟪ $a:ptf -> $b:ptf ⟫) => `(⟪ $a ⇒ $b ⟫)
  | `(⟪ $a:ptf <= $b:ptf ⟫) => `(⟪ $a ≤ $b ⟫)
  | `(⟪ $a:ptf >= $b:ptf ⟫) => `(⟪ $a ≥ $b ⟫)
  | `(⟪ $a:ptf != $b:ptf ⟫) => `(⟪ $a ≠ $b ⟫)
  | `(⟪ $a:ptf % $b:ptf ⟫) => `(⟪ $a mod $b ⟫)
  | `(⟪ $a:ptf /\ $b:ptf ⟫) => `(⟪ $a ∧ $b ⟫)
  | `(⟪ $a:ptf \/ $b:ptf ⟫) => `(⟪ $a ∨ $b ⟫)
  | `(⟪ ~ $a:ptf ⟫) => `(⟪ ¬ $a ⟫)
  | `(⟪ forall $i:ident : $r:ptf : $b:ptf ⟫) => `(⟪ ∀ $i : $r : $b ⟫)
  | `(⟪ exists $i:ident : $r:ptf : $b:ptf ⟫) => `(⟪ ∃ $i : $r : $b ⟫)
  | `(⟪ wp($S:ptcmd) ⟫) => do
    let some (S', R) := wpSplit S.raw | Macro.throwError "wp(S, R) needs a postcondition"
    let σ := mkIdent `σ
    `(PT.wp ⟦$(⟨S'⟩):ptcmd⟧ (fun ($σ : $(mkIdent `St)) => ⟪$(⟨R⟩):ptf⟫) $σ)
  | `(⟪ $n:num ⟫) => `(($n : Int))
  | `(⟪ ($f:ptf) ⟫) => `((⟪$f⟫))
  | `(⟪ - $a:ptf ⟫) => `(- ⟪$a⟫)
  | `(⟪ $a:ptf ^ $n:num ⟫) => `(⟪$a⟫ ^ $n)
  | `(⟪ $a:ptf * $b:ptf ⟫) => `(⟪$a⟫ * ⟪$b⟫)
  | `(⟪ $a:ptf / $b:ptf ⟫) => `(⟪$a⟫ / ⟪$b⟫)
  | `(⟪ $a:ptf mod $b:ptf ⟫) => `(⟪$a⟫ % ⟪$b⟫)
  | `(⟪ $a:ptf + $b:ptf ⟫) => `(⟪$a⟫ + ⟪$b⟫)
  | `(⟪ $a:ptf - $b:ptf ⟫) => `(⟪$a⟫ - ⟪$b⟫)
  | `(⟪ $a:ptf < $b:ptf ⟫) => `(⟪$a⟫ < ⟪$b⟫)
  | `(⟪ $a:ptf ≤ $b:ptf ⟫) => `(⟪$a⟫ ≤ ⟪$b⟫)
  | `(⟪ $a:ptf > $b:ptf ⟫) => `(⟪$a⟫ > ⟪$b⟫)
  | `(⟪ $a:ptf ≥ $b:ptf ⟫) => `(⟪$a⟫ ≥ ⟪$b⟫)
  | `(⟪ $a:ptf ≠ $b:ptf ⟫) => `(⟪$a⟫ ≠ ⟪$b⟫)
  | `(⟪ $a:ptf ≤ $b:ptf < $c:ptf ⟫) => `(⟪$a⟫ ≤ ⟪$b⟫ ∧ ⟪$b⟫ < ⟪$c⟫)
  | `(⟪ $a:ptf ≤ $b:ptf ≤ $c:ptf ⟫) => `(⟪$a⟫ ≤ ⟪$b⟫ ∧ ⟪$b⟫ ≤ ⟪$c⟫)
  | `(⟪ $a:ptf < $b:ptf < $c:ptf ⟫) => `(⟪$a⟫ < ⟪$b⟫ ∧ ⟪$b⟫ < ⟪$c⟫)
  | `(⟪ $a:ptf < $b:ptf ≤ $c:ptf ⟫) => `(⟪$a⟫ < ⟪$b⟫ ∧ ⟪$b⟫ ≤ ⟪$c⟫)
  | `(⟪ ¬ $f:ptf ⟫) => `(¬ ⟪$f⟫)
  | `(⟪ $f:ptf ∧ $g:ptf ⟫) => `(⟪$f⟫ ∧ ⟪$g⟫)
  | `(⟪ $f:ptf ∨ $g:ptf ⟫) => `(⟪$f⟫ ∨ ⟪$g⟫)
  | `(⟪ $f:ptf ⇒ $g:ptf ⟫) => `(PT.Imp ⟪$f⟫ ⟪$g⟫)
  | `(⟪ $f:ptf = $g:ptf ⟫) => `(pt_eq% $f $g)
  -- an interval range makes the dummy an integer
  | `(⟪ ∀ $i:ident : $a:ptf ≤ $j:ptf < $b:ptf : $body:ptf ⟫) =>
    `(PT.Forall (fun ($i : Int) => ⟪$a⟫ ≤ ⟪$j⟫ ∧ ⟪$j⟫ < ⟪$b⟫) (fun ($i : Int) => ⟪$body⟫))
  | `(⟪ ∀ $i:ident : $a:ptf ≤ $j:ptf ≤ $b:ptf : $body:ptf ⟫) =>
    `(PT.Forall (fun ($i : Int) => ⟪$a⟫ ≤ ⟪$j⟫ ∧ ⟪$j⟫ ≤ ⟪$b⟫) (fun ($i : Int) => ⟪$body⟫))
  | `(⟪ ∀ $i:ident : $a:ptf < $j:ptf < $b:ptf : $body:ptf ⟫) =>
    `(PT.Forall (fun ($i : Int) => ⟪$a⟫ < ⟪$j⟫ ∧ ⟪$j⟫ < ⟪$b⟫) (fun ($i : Int) => ⟪$body⟫))
  | `(⟪ ∀ $i:ident : $a:ptf < $j:ptf ≤ $b:ptf : $body:ptf ⟫) =>
    `(PT.Forall (fun ($i : Int) => ⟪$a⟫ < ⟪$j⟫ ∧ ⟪$j⟫ ≤ ⟪$b⟫) (fun ($i : Int) => ⟪$body⟫))
  | `(⟪ ∃ $i:ident : $a:ptf ≤ $j:ptf < $b:ptf : $body:ptf ⟫) =>
    `(PT.Ex (fun ($i : Int) => ⟪$a⟫ ≤ ⟪$j⟫ ∧ ⟪$j⟫ < ⟪$b⟫) (fun ($i : Int) => ⟪$body⟫))
  | `(⟪ ∃ $i:ident : $a:ptf ≤ $j:ptf ≤ $b:ptf : $body:ptf ⟫) =>
    `(PT.Ex (fun ($i : Int) => ⟪$a⟫ ≤ ⟪$j⟫ ∧ ⟪$j⟫ ≤ ⟪$b⟫) (fun ($i : Int) => ⟪$body⟫))
  | `(⟪ ∃ $i:ident : $a:ptf < $j:ptf < $b:ptf : $body:ptf ⟫) =>
    `(PT.Ex (fun ($i : Int) => ⟪$a⟫ < ⟪$j⟫ ∧ ⟪$j⟫ < ⟪$b⟫) (fun ($i : Int) => ⟪$body⟫))
  | `(⟪ ∃ $i:ident : $a:ptf < $j:ptf ≤ $b:ptf : $body:ptf ⟫) =>
    `(PT.Ex (fun ($i : Int) => ⟪$a⟫ < ⟪$j⟫ ∧ ⟪$j⟫ ≤ ⟪$b⟫) (fun ($i : Int) => ⟪$body⟫))
  | `(⟪ ∀ $i:ident : $r:ptf : $b:ptf ⟫) => `(PT.Forall (fun $i => ⟪$r⟫) (fun $i => ⟪$b⟫))
  | `(⟪ ∃ $i:ident : $r:ptf : $b:ptf ⟫) => `(PT.Ex (fun $i => ⟪$r⟫) (fun $i => ⟪$b⟫))

  | `(⟪ $f:ptf ⟫) => do
    -- `wp(S, P)` also parses as an application of `wp`, so take the `wp` reading
    if f.raw.isOfKind choiceKind then
      if let some w := f.raw.getArgs.find? (·.getKind == ``ptWp) then
        return ← `(⟪$(⟨w⟩):ptf⟫)

    let k := f.raw.getKind
    let sec : Option Name :=
      if k == ``ptSecEq then some ``PT.SecEq else if k == ``ptSecLt then some ``PT.SecLt
      else if k == ``ptSecGt then some ``PT.SecGt else if k == ``ptSecLe then some ``PT.SecLe
      else if k == ``ptSecGe then some ``PT.SecGe else if k == ``ptSecNe then some ``PT.SecNe
      else none
    if k == ``ptApp then
      let g : Ident := ⟨f.raw[0]⟩
      let args ← f.raw[2].getSepArgs.mapM fun a => `(⟪$(⟨a⟩):ptf⟫)
      `($g $args*)
    else if k == ``ptIndex then
      let a : TSyntax `ptf := ⟨f.raw[0]⟩
      let i : TSyntax `ptf := ⟨f.raw[2]⟩
      `(⟪$a⟫ ⟪$i⟫)
    else if k == ``ptUpd then
      let b : TSyntax `ptf := ⟨f.raw[1]⟩
      let i : TSyntax `ptf := ⟨f.raw[3]⟩
      let e : TSyntax `ptf := ⟨f.raw[5]⟩
      `(PT.upd ⟪$b⟫ ⟪$i⟫ ⟪$e⟫)
    else if let some c := sec then
      let b : TSyntax `ptf := ⟨f.raw[0]⟩
      let i : TSyntax `ptf := ⟨f.raw[2]⟩
      let j : TSyntax `ptf := ⟨f.raw[4]⟩
      let x : TSyntax `ptf := ⟨f.raw[7]⟩
      `($(mkIdent c) ⟪$b⟫ ⟪$i⟫ ⟪$j⟫ ⟪$x⟫)
    else if k == ``ptSecMem then
      let x : TSyntax `ptf := ⟨f.raw[0]⟩
      let b : TSyntax `ptf := ⟨f.raw[2]⟩
      let i : TSyntax `ptf := ⟨f.raw[4]⟩
      let j : TSyntax `ptf := ⟨f.raw[6]⟩
      `(PT.SecMem ⟪$x⟫ ⟪$b⟫ ⟪$i⟫ ⟪$j⟫)
    else Macro.throwUnsupported

end PT
