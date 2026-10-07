import PT.Syntax

open Lean Elab Command Meta

set_option pt.strict false

namespace PT

syntax ptLoop := "do " ptGuard ((" □ " <|> " | ") ptGuard)* &"od"
syntax ptAnnot := "{" ident " : " ptf "}"
syntax (name := programCmd) "program " ident ptAnnot (ptcmd)?
  "{" &"inv" ident " : " ptf "}" "{" &"bound" ident " : " ptf "}"
  ptLoop (ptcmd)? ptAnnot : command
syntax (name := programIfCmd) "program " ident ptAnnot
  "if " ptGuard ((" □ " <|> " | ") ptGuard)* &"fi" ptAnnot : command

private def sub (i : Nat) : String :=
  String.map (fun c => Char.ofNat (c.toNat - '0'.toNat + 0x2080)) (toString i)

private def rQ := "the precondition Q"
private def rP := "the invariant P"
private def rR := "the postcondition R"

/-- Obligations of a loop with their forms in the notation of the appendix. -/
def obligations (init : Option (TSyntax `ptcmd)) (Q P t : TSyntax `ptf)
    (guards : Array (TSyntax `ptf × TSyntax `ptcmd)) (fin : Option (TSyntax `ptcmd))
    (R : TSyntax `ptf) : MacroM (Array (String × TSyntax `ptf × ObRoles)) := do
  let mut out := #[]
  let one := guards.size == 1
  let bn (i : Nat) := if one then "B" else s!"B{sub i}"
  let sn (i : Nat) := if one then "S" else s!"S{sub i}"
  let bbs := " ∨ ".intercalate ((List.range guards.size).map fun i => bn (i + 1))
  let bbp := if one then "B" else s!"({bbs})"
  let wpOr (S : Option (TSyntax `ptcmd)) (A : TSyntax `ptf) : MacroM (TSyntax `ptf) :=
    match S with
    | some S => `(ptf| wp($S:ptcmd, $A:ptf))
    | none => pure A
  out := out.push ("init", ← `(ptf| ($Q) ⇒ $(← wpOr init P)), match init with
    | some _ => { template := "Q ⇒ wp(S₀, P)", ante := #[rQ], cmdSym := "S₀",
                  postSym := "P" }
    | none => { template := "Q ⇒ P", ante := #[rQ], cons := rP })
  for (B, S) in guards, i in [1:guards.size + 1] do
    out := out.push (if one then "inv" else s!"inv{i}", ← `(ptf| ($P) ∧ ($B) ⇒ wp($S:ptcmd, $P:ptf)),
      { template := s!"P ∧ {bn i} ⇒ wp({sn i}, P)", ante := #[rP, s!"the guard {bn i}"], cmdSym := sn i, postSym := "P" })
  let BB ← guards[1:].foldlM (init := guards[0]!.1) fun acc (B, _) => `(ptf| $acc ∨ $B)
  let negRole := if one then "the negated guard ¬B, with B the guard as written in the program"
    else s!"the negated guards ¬{bbp}, with the guards as written in the program"
  out := out.push ("post", ← `(ptf| ($P) ∧ ¬($BB) ⇒ $(← wpOr fin R)), match fin with
    | some _ => { template := s!"P ∧ ¬{bbp} ⇒ wp(Sf, R)", ante := #[rP, negRole], cmdSym := "Sf", postSym := "R" }
    | none => { template := s!"P ∧ ¬{bbp} ⇒ R", ante := #[rP, negRole], cons := rR })
  out := out.push ("bound", ← `(ptf| ($P) ∧ ($BB) ⇒ 0 < $t),
    { template := s!"P ∧ {bbp} ⇒ 0 < t", ante := #[rP, if one then "the guard B" else s!"the guards {bbs}"],
      cons := "0 < t", note := "t is the bound of the program" })
  let t1 : TSyntax `ptf ← `(ptf| $(mkIdent `t1):ident)
  let save : TSyntax `ptcmd ← `(ptcmd| $(mkIdent `t1):ident := $t)
  for (B, S) in guards, i in [1:guards.size + 1] do
    out := out.push (if one then "dec" else s!"dec{i}",
      ← `(ptf| ($P) ∧ ($B) ⇒ wp($save:ptcmd; $S:ptcmd, $t < $t1)),
      { template := s!"P ∧ {bn i} ⇒ wp(t1 := t; {sn i}, t < t1)", ante := #[rP, s!"the guard {bn i}"],
        cmdSym := s!"t1 := t; {sn i}", postSym := "t < t1", note := "t is the bound of the program" })
  return out

/-- The Alternative Command Theorem. -/
def ifObligations (Q R : TSyntax `ptf) (guards : Array (TSyntax `ptf × TSyntax `ptcmd)) :
    MacroM (Array (String × TSyntax `ptf × ObRoles)) := do
  let bbs := " ∨ ".intercalate ((List.range guards.size).map fun i => s!"B{sub (i + 1)}")
  let BB ← guards[1:].foldlM (init := guards[0]!.1) fun acc (B, _) => `(ptf| $acc ∨ $B)
  let gf ← `(ptf| ($Q) ⇒ ($BB))
  let gr : ObRoles := { template := s!"Q ⇒ {bbs}", ante := #[rQ], cons := s!"the guards {bbs}" }
  let mut out := #[("guards", gf, gr)]
  for (B, S) in guards, i in [1:guards.size + 1] do
    out := out.push (s!"branch{i}", ← `(ptf| ($Q) ∧ ($B) ⇒ wp($S:ptcmd, $R:ptf)),
      { template := s!"Q ∧ B{sub i} ⇒ wp(S{sub i}, R)", ante := #[rQ, s!"the guard B{sub i}"],
        cmdSym := s!"S{sub i}", postSym := "R" })
  return out

/-- What the symbols of the obligation forms stand for, per program. -/
initialize legendExt : EnvExtension (NameMap String) ← registerEnvExtension (pure {})

private def guardList (n : Nat) : String :=
  if n == 1 then "B → S the guarded command"
  else ", ".intercalate ((List.range n).map fun i => s!"B{sub (i + 1)} → S{sub (i + 1)}") ++ " the guarded commands"

private def defineObligations (name : Name) (obs : Array (String × TSyntax `ptf × ObRoles)) (legend : String) :
    CommandElabM Unit := do
  for (ob, f, roles) in obs do
    let n := name ++ Name.mkSimple ob
    elabCommand (← `(def $(mkIdent (n ++ `ob)) ($(mkIdent `σ) : $(mkIdent `St)) : Prop := ⟪$f⟫))
    modifyEnv (obRolesExt.modifyState · (·.insert n roles))
  modifyEnv (legendExt.modifyState · (·.insert name legend))

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
  let items := ["Q and R are the pre- and postcondition", "P the invariant", "t the bound", guardList guards.size] ++
    (if init.isSome then ["S₀ the initialization"] else []) ++ (if fin.isSome then ["Sf the final command"] else [])
  let legend := ", ".intercalate items.dropLast ++ " and " ++ items.getLast!
  defineObligations name.getId (← liftMacroM (obligations init Q P t guards fin R)) legend

@[command_elab programIfCmd] def elabProgramIf : CommandElab := fun stx => do
  if stx.hasMissing then return
  let name : Ident := ⟨stx[1]⟩
  let Q : TSyntax `ptf := ⟨stx[2][3]⟩
  let guards : Array (TSyntax `ptf × TSyntax `ptcmd) :=
    (#[stx[4]] ++ stx[5].getArgs.map (·[1])).map fun g => (⟨g[0]⟩, ⟨g[2]⟩)
  let R : TSyntax `ptf := ⟨stx[7][3]⟩
  if (← liftTermElabM stateName?).isNone then
    throwErrorAt name "declare the program variables with `state` first"
  let legend := s!"Q and R are the pre- and postcondition and " ++
    (if guards.size == 1 then "B₁ → S₁ the guarded command" else
      ", ".intercalate ((List.range guards.size).map fun i => s!"B{sub (i + 1)} → S{sub (i + 1)}") ++ " the guarded commands")
  defineObligations name.getId (← liftMacroM (ifObligations Q R guards)) legend

/-- Generated obligations in appendix order. -/
def obligationsOf (env : Environment) (name : Name) : Array Name := Id.run do
  let mut out := #[]
  for (n, _) in env.constants.map₂.toList do
    if n.getString! == "ob" && n.getPrefix.getPrefix == name then out := out.push n.getPrefix
  let rank (n : Name) : Nat :=
    let s := n.getString!
    let base := String.ofList (s.toList.takeWhile Char.isAlpha)
    let num := (String.ofList (s.toList.dropWhile Char.isAlpha)).toNat?.getD 0
    10 * (["guards", "branch", "init", "inv", "post", "bound", "dec"].idxOf? base |>.getD 9) + num
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
  for first in [`init, `guards] do
    let ob ← resolveProofRef (mkIdentFrom id (id.getId ++ first ++ `ob))
    if (← getEnv).contains ob then return ob.getPrefix.getPrefix
  return id.getId

syntax (name := obligationsCmd) "obligations " ident : command
@[command_elab obligationsCmd] def elabObligations : CommandElab := fun stx => do
  let name ← resolveProgramRef stx[1]
  let env ← getEnv
  let obs := obligationsOf env name
  if obs.isEmpty then throwError "no `program {name}`"
  let roles := obRolesExt.getState env
  let lines := obs.map fun n => m!"\n  proof {n} : {((roles.find? n).map (·.template)).getD "?"}"
  let legend := ((legendExt.getState env).find? name).getD ""
  logInfo (lines.foldl (· ++ ·) m!"obligations of {name}, in the notation of the appendix" ++ m!"\nwhere {legend}")

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
