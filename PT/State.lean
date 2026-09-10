import Lean
import PT.Programs
import PT.Formula

open Lean Elab Command Meta PrettyPrinter Delaborator SubExpr

namespace PT

syntax (name := stateCmd) "state " sepBy1(ident+ " : " term, ", ") : command

@[command_elab stateCmd] def elabState : CommandElab := fun stx => do
  if (← liftTermElabM stateName?).isSome then
    throwError "a file has one `state` line, add these variables to it"
  let mut src := "private structure St where\n"
  for g in stx[1].getSepArgs do
    let ty := if g[2].isIdent && g[2].getId == `Array then "PT.Arr" else g[2].reprint.get!
    for x in g[0].getArgs do
      src := src ++ s!"  {x.getId} : {ty}\n"
  match Parser.runParserCategory (← getEnv) `command src with
  | .ok cmd => elabCommand cmd
  | .error e => throwError e

/-- Hide the state in fields, array indexing, and predicate applications. -/
@[delab app] def delabStateApp : Delab := do
  let e ← getExpr
  let isσ (fid : FVarId) : DelabM Bool := do
    return ((← getLCtx).find? fid).any (·.userName == `σ)
  if let .app (.app (.const n _) (.fvar fid)) _ := e then
    if (← isσ fid) && ((← getEnv).getProjectionFnInfo? n).isSome then
      let b := mkIdent (Name.mkSimple n.getString!)
      let i ← withAppArg delab
      return ← `($b[$i])
  let .app f a := e | failure
  let .fvar fid := a | failure
  unless ← isσ fid do failure
  match f with
  | .const n _ =>
    unless ((← getEnv).getProjectionFnInfo? n).isSome do failure
    return mkIdent (Name.mkSimple n.getString!)
  | .fvar pf =>
    unless (← whnfR (← inferType f)).isArrow do failure
    return mkIdent (← pf.getUserName)
  | _ => failure

declare_syntax_cat cmdT (behavior := both)
syntax &"skip" : cmdT
syntax &"abort" : cmdT
syntax ident : cmdT
syntax ident,+ " := " term,+ : cmdT
syntax:10 cmdT:11 "; " cmdT:10 : cmdT
syntax (name := cmdIf) "if " sepBy1(term:30 " → " cmdT, " □ ") &" fi" : cmdT
syntax "(" cmdT ")" : cmdT
syntax:max "wp" noWs "(" cmdT ", " term ")" : term

private partial def instFields (stx : Syntax) : Array (Syntax × Syntax) := Id.run do
  let mut out := #[]
  if stx.getKind == ``Parser.Term.structInstField then
    if let some d := stx.find? (·.getKind == ``Parser.Term.structInstFieldDef) then
      return #[(stx[0][0], d[2])]
  for a in stx.getArgs do out := out ++ instFields a
  return out

private def changedFields (stx : Syntax) : Array (Ident × Term) :=
  (instFields stx).filterMap fun (name, val) =>
    if val.isIdent && name.isIdent && val.getId == name.getId then none
    else some (⟨name⟩, ⟨val⟩)

-- explicit forms, so that `cmdOf` sees `PT.Cmd.seq a b` rather than `a.seq b`
@[app_unexpander PT.Cmd.seq] def unexpandSeq : Unexpander
  | `($_ $a $b) => `(PT.Cmd.seq $a $b)
  | _ => throw ()
@[app_unexpander PT.Cmd.assign] def unexpandAssign : Unexpander
  | `($_ $f) => `(PT.Cmd.assign $f)
  | _ => throw ()
@[app_unexpander PT.Cmd.ifc] def unexpandIfc : Unexpander
  | `($_ $l) => `(PT.Cmd.ifc $l)
  | _ => throw ()

partial def cmdOf : Term → UnexpandM (TSyntax `cmdT)
  | `(PT.Cmd.seq $a $b) => do `(cmdT| $(← cmdOf a); $(← cmdOf b))
  | `(PT.Cmd.assign fun $_ => $inst) => do
    let fs := changedFields inst.raw
    if fs.isEmpty then throw ()
    let xs : Syntax.TSepArray `ident "," := .ofElems (fs.map (·.1))
    let es : Syntax.TSepArray `term "," := .ofElems (fs.map (·.2))
    `(cmdT| $xs:ident,* := $es:term,*)
  | `(PT.Cmd.ifc [$elems,*]) => do
    let mut Bs : Array Term := #[]
    let mut Ss : Array (TSyntax `cmdT) := #[]
    for e in elems.getElems do
      match e with
      | `(($B, $S)) =>
        Bs := Bs.push (← match B with
          | `(fun $_ => $body) => pure body
          | b => pure b)
        Ss := Ss.push (← cmdOf S)
      | _ => throw ()
    match Bs, Ss with
    | #[B₁], #[S₁] => `(cmdT| if $B₁ → $S₁ fi)
    | #[B₁, B₂], #[S₁, S₂] => `(cmdT| if $B₁ → $S₁ □ $B₂ → $S₂ fi)
    | #[B₁, B₂, B₃], #[S₁, S₂, S₃] => `(cmdT| if $B₁ → $S₁ □ $B₂ → $S₂ □ $B₃ → $S₃ fi)
    | _, _ => throw ()
  | `($S:ident) =>
    let n := S.getId.eraseMacroScopes
    if n.getString! == "skip" && n.getNumParts > 1 then `(cmdT| $(mkIdent `skip):ident)
    else if n.getString! == "abort" && n.getNumParts > 1 then `(cmdT| $(mkIdent `abort):ident)
    else `(cmdT| $S:ident)
  | _ => throw ()

@[app_unexpander PT.wp] def unexpandWp : Unexpander
  | `($_ $S $R $_) => do
    let R ← match R with
      | `(fun $_ => $body) => pure body
      | r => pure r
    `(wp($(← cmdOf S), $R))
  | _ => throw ()

end PT
