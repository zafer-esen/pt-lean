import PT.Syntax

open Lean Elab Command Meta

set_option pt.strict false

namespace PT

syntax ptLoop := "do " ptGuard ((" □ " <|> " | ") ptGuard)* &"od"
syntax ptAnnot := "{" ident " : " ptf "}"
syntax (name := programCmd) "program " ident ptAnnot (ptcmd)?
  "{" &"inv" ident " : " ptf "}" "{" &"bound" ident " : " ptf "}"
  ptLoop (ptcmd)? ptAnnot : command

def obligations (init : Option (TSyntax `ptcmd)) (Q P t : TSyntax `ptf)
    (guards : Array (TSyntax `ptf × TSyntax `ptcmd)) (fin : Option (TSyntax `ptcmd))
    (R : TSyntax `ptf) : MacroM (Array (String × TSyntax `ptf)) := do
  let mut out := #[]
  let one := guards.size == 1
  let wpOr (S : Option (TSyntax `ptcmd)) (A : TSyntax `ptf) : MacroM (TSyntax `ptf) :=
    match S with
    | some S => `(ptf| wp($S:ptcmd, $A:ptf))
    | none => pure A
  out := out.push ("init", ← `(ptf| ($Q) ⇒ $(← wpOr init P)))
  for (B, S) in guards, i in [1:guards.size + 1] do
    out := out.push (if one then "inv" else s!"inv{i}", ← `(ptf| ($P) ∧ ($B) ⇒ wp($S:ptcmd, $P:ptf)))
  let BB ← guards[1:].foldlM (init := guards[0]!.1) fun acc (B, _) => `(ptf| $acc ∨ $B)
  out := out.push ("post", ← `(ptf| ($P) ∧ ¬($BB) ⇒ $(← wpOr fin R)))
  out := out.push ("bound", ← `(ptf| ($P) ∧ ($BB) ⇒ 0 < $t))
  let t1 : TSyntax `ptf ← `(ptf| $(mkIdent `t1):ident)
  let save : TSyntax `ptcmd ← `(ptcmd| $(mkIdent `t1):ident := $t)
  for (B, S) in guards, i in [1:guards.size + 1] do
    out := out.push (if one then "dec" else s!"dec{i}",
      ← `(ptf| ($P) ∧ ($B) ⇒ wp($save:ptcmd; $S:ptcmd, $t < $t1)))
  return out

private partial def savedBoundUse? (env : Environment) (stx : Syntax) : Option Syntax :=
  if stx.isIdent && stx.getId == `t1 then some stx
  else if let some text := stx.isStrLit? then
    match Parser.runParserCategory env `ptcmd text with
    | .ok cmd => (savedBoundUse? env cmd).map fun _ => stx
    | .error _ => none
  else stx.getArgs.findSome? (savedBoundUse? env)

@[command_elab programCmd] def elabProgram : CommandElab := fun stx => do
  if stx.hasMissing then return
  let name : Ident := ⟨stx[1]⟩
  let Q : TSyntax `ptf := ⟨stx[2][3]⟩
  let init : Option (TSyntax `ptcmd) := if stx[3].getNumArgs > 0 then some ⟨stx[3][0]⟩ else none
  let P : TSyntax `ptf := ⟨stx[8]⟩
  let t : TSyntax `ptf := ⟨stx[14]⟩
  let loop := stx[16]
  let guards : Array (TSyntax `ptf × TSyntax `ptcmd) :=
    (#[loop[1]] ++ loop[2].getArgs.map (·[1])).map fun g => (⟨g[0]⟩, ⟨g[2]⟩)
  let fin : Option (TSyntax `ptcmd) := if stx[17].getNumArgs > 0 then some ⟨stx[17][0]⟩ else none
  let R : TSyntax `ptf := ⟨stx[18][3]⟩
  let env ← getEnv
  let parts := #[Q.raw, P.raw, t.raw, R.raw] ++
    (init.toArray ++ fin.toArray).map (·.raw) ++
    guards.flatMap fun (B, S) => #[B.raw, S.raw]
  for part in parts do
    if let some use := savedBoundUse? env part then
      throwErrorAt use "`t1` is reserved for the saved bound; use another name in program code and annotations"
  liftTermElabM do
    let msg := "declare the saved bound as `t1 : Int` in `state`"
    let some st ← stateName? | throwErrorAt name msg
    let some info := env.find? (st ++ `t1) | throwErrorAt name msg
    forallBoundedTelescope info.type (some 1) fun _ ty => do
      unless ← isDefEq ty (mkConst ``Int) do throwErrorAt name msg
  let obs ← liftMacroM (obligations init Q P t guards fin R)
  for (ob, f) in obs do
    let n := mkIdent (name.getId ++ Name.mkSimple ob)

    elabCommand (← `(def $(mkIdent (n.getId ++ `ob)) ($(mkIdent `σ) : $(mkIdent `St)) : Prop := ⟪$f⟫))

/-- Generated obligations in appendix order. -/
def obligationsOf (env : Environment) (name : Name) : Array Name := Id.run do
  let mut out := #[]
  for (n, _) in env.constants.map₂.toList do
    if n.getString! == "ob" && n.getPrefix.getPrefix == name then out := out.push n.getPrefix
  let rank (n : Name) : Nat :=
    let s := n.getString!
    let base := String.ofList (s.toList.takeWhile Char.isAlpha)
    let num := (String.ofList (s.toList.dropWhile Char.isAlpha)).toNat?.getD 0
    10 * (["init", "inv", "post", "bound", "dec"].idxOf? base |>.getD 9) + num
  return out.qsort fun a b => rank a < rank b

def obligationLines (name : Name) : CommandElabM (Array MessageData) := do
  let env ← getEnv
  let mut out := #[]
  for n in obligationsOf env name do
    let some ci := env.find? (n ++ `ob) | continue
    let some v := ci.value? | continue
    let text ← liftTermElabM <| Meta.lambdaTelescope v fun _ body => do
      return toString (← Meta.ppExpr body)
    out := out.push m!"{n} : {text}"
  return out

private def resolveProgramRef (id : Syntax) : CommandElabM Name := do
  let ob ← resolveProofRef (mkIdentFrom id (id.getId ++ `init.ob))
  return ob.getPrefix.getPrefix

syntax (name := obligationsCmd) "obligations " ident : command
@[command_elab obligationsCmd] def elabObligations : CommandElab := fun stx => do
  let name ← resolveProgramRef stx[1]
  let lines ← obligationLines name
  if lines.isEmpty then throwError "no `program {name}`"
  logInfo (lines.foldl (fun acc l => acc ++ m!"\n  proof " ++ l) m!"obligations of {name}:")

syntax (name := verifiedCmd) "verified " ident : command
@[command_elab verifiedCmd] def elabVerified : CommandElab := fun stx => do
  let name ← resolveProgramRef stx[1]
  let obs := obligationsOf (← getEnv) name
  if obs.isEmpty then throwError "no `program {name}`"
  let mut problems : Array MessageData := #[]
  for n in obs do
    if let some issue := (← checkProof n).issue? then
      problems := problems.push m!"{n}: {issue}"
  unless problems.isEmpty do
    throwError (problems.foldl (fun acc p => acc ++ m!"\n  " ++ p) m!"{name}: not verified")
  logInfo ((← obligationLines name).foldl (fun acc l => acc ++ m!"\n  " ++ l) m!"{name}: verified ({obs.size} obligations)")

end PT
