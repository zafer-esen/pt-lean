import PT.Step
import PT.HintParser
import PT.Formula
import PT.State

open Lean Elab Command

set_option pt.strict false

namespace PT

syntax ptStepEq  := "=" "{" hintText "}" ptf
syntax ptStepImp := "⇒" "{" hintText "}" ptf
syntax ptAssume := (&"assume" <|> &"Assume") ptf,+

syntax ptBinder := "(" ident+ (" : " term)? ")"
syntax (name := proofCmd)
  "proof" (ident)? (ptBinder)* ":" ptf (ptAssume)? (ptf)? (ptStepEq <|> ptStepImp)* "qed" : command

partial def stripParens (f : Syntax) : Syntax :=
  if f.getNumArgs == 3 && f[0].isAtom && f[0].getAtomVal == "(" && f[2].isAtom && f[2].getAtomVal == ")"
  then stripParens f[1] else f

/-- A quantifier body need not use its dummy. -/
@[unused_variables_ignore_fn]
def ignoreProofVariables : Linter.IgnoreFunction := fun _ stack _ =>
  stack.any fun (s, _) => s.getKind == ``proofCmd

/-- Add the current state before the explicit proof variables. -/
def headerBinders (gs : Array Syntax) : CommandElabM (Array (TSyntax ``Parser.Term.bracketedBinder)) := do
  let St := mkIdent `St
  let σ := mkIdent `σ
  let tyOf (g : Syntax) : Name := if g[2].getNumArgs > 0 && g[2][1].isIdent then g[2][1].getId else .anonymous
  let usesSt := gs.any fun g => tyOf g == `Cmd || tyOf g == `Pred
  let mut binders : Array (TSyntax ``Parser.Term.bracketedBinder) := #[]
  let stName? ← liftTermElabM stateName?
  if stName?.isSome then
    binders := binders.push (← `(bracketedBinder| ($σ:ident : $St)))
  else if usesSt then
    binders := binders.push (← `(bracketedBinder| {$St:ident : Type}))
    binders := binders.push (← `(bracketedBinder| ($σ:ident : $St)))
  for g in gs do
    let ids : Array Ident := g[1].getArgs.map (⟨·⟩)
    let ty : Term ← match tyOf g with
      | `Cmd => `(PT.Cmd $St) | `Pred => `(PT.Pred $St) | `Array => `(PT.Arr)
      | .anonymous => if g[2].getNumArgs > 0 then pure ⟨g[2][1]⟩ else `(Prop)
      | _ => pure ⟨g[2][1]⟩
    binders := binders.push (← `(bracketedBinder| ($ids* : $ty)))
  return binders

def anonName (stx : Syntax) : CommandElabM Ident := do
  let line := ((← getFileMap).toPosition (stx.getPos?.getD 0)).line
  return mkIdent (Name.mkSimple s!"line {line} of {(← getMainModule).getString!}")

/-- Compare with `n.ob` up to associativity and commutativity. Accept if no obligation exists. -/
def statesObligation (n : Name) : CommandElabM Bool := do
  let env ← getEnv
  let some ci := env.find? n | return false
  let some ob := env.find? (n ++ `ob) | return true
  liftTermElabM do
    let .forallE _ St _ _ := ob.type | return false
    Meta.withLocalDeclD `σ St fun σ => do
      let a ← Meta.instantiateForall ci.type #[σ]
      if ← (try Meta.isDefEq a (mkApp (mkConst (n ++ `ob)) σ) catch _ => pure false) then return true
      let some v := ob.value? | return false
      return acNorm (← instantiateMVars a) == acNorm (← Meta.instantiateLambda v #[σ])

structure ProofCheck where
  present : Bool := false
  block : Bool := false
  complete : Bool := false
  axiomatic : Bool := false
  relaxed : Bool := false
  matchesObligation : Bool := true

def ProofCheck.issue? (c : ProofCheck) : Option String :=
  if !c.present then some "missing"
  else if !c.block then some "not a proof block"
  else if !c.complete then some "not proved"
  else if c.axiomatic then some "rests on an axiom of the file"
  else if c.relaxed then some "checked with weakened options"
  else if !c.matchesObligation then some "does not state the obligation of `program`"
  else none

def checkProof (n : Name) : CommandElabM ProofCheck := do
  let env ← getEnv
  let some ci := env.find? n | return {}
  unless ci.isTheorem do return { present := true }
  let axioms ← liftCoreM (collectAxioms n)
  return {
    present := true
    block := proofTag.hasTag env n
    complete := !axioms.contains ``sorryAx
    axiomatic := axioms.any fun a => ![``sorryAx, ``propext, ``Classical.choice, ``Quot.sound].contains a
    relaxed := relaxedTag.hasTag env n
    matchesObligation := ← statesObligation n
  }

def resolveProofRef (id : Syntax) : CommandElabM Name := do
  let candidates := (← resolveGlobalName id.getId).filterMap fun (n, fields) =>
    if fields.isEmpty then some n else none
  if candidates.isEmpty then return id.getId
  ensureNonAmbiguous id candidates

def relaxedOptions : CommandElabM Bool := do
  let opts ← getOptions
  return !pt.strict.get opts || !pt.check.get opts
    || (appendixExt.getState (← getEnv)).any (· != pt.sections.get opts)

@[command_elab proofCmd] def elabProof : CommandElab := fun stx => do

  if stx.hasMissing then return
  let name? : Option Ident := if stx[1].getNumArgs > 0 then some ⟨stx[1][0]⟩ else none

  if let some n := name? then
    if n.getId.components.any (·.toString.startsWith "_") then throwErrorAt n "a name may not start with `_`"
  let relaxed ← relaxedOptions
  let σ := mkIdent `σ
  let stName? ← liftTermElabM stateName?
  let binders ← headerBinders stx[2].getArgs

  liftTermElabM <| Term.withAutoBoundImplicit <| Term.elabBinders binders fun xs => do
    for x in xs do
      let ty ← Meta.inferType x
      if ← Meta.isProp ty then
        throwErrorAt stx[2] "`{← Meta.ppExpr ty}` is an assumption, not a variable. Write it in an `assume` line"

  let stmt : TSyntax `ptf ← liftTermElabM <| Term.withAutoBoundImplicit <|
    Term.elabBinders binders fun _ => do pure ⟨← reassoc stx[4]⟩
  let stmt : TSyntax `ptf := ⟨stripParens stmt⟩
  let assumptions : Array (TSyntax `ptf) :=
    if stx[5].getNumArgs > 0 then stx[5][0][1].getSepArgs.map (⟨·⟩) else #[]
  let steps := stx[7].getArgs

  if stx[6].getNumArgs == 0 && !steps.isEmpty then
    throwErrorAt steps[0]! "the calculation must start with its first line, usually the left side of the statement, or the consequent under `assume`"
  let first : TSyntax `ptf := if stx[6].getNumArgs > 0 then ⟨stx[6][0]⟩ else stmt

  if steps.isEmpty then
    logWarningAt stx[4] "not proved yet"
    let stmtT ← `(⟪$stmt⟫)
    let cmd ← match name? with
      | some n =>
        if relaxed then `(@[pt_proof, pt_relaxed] theorem $n:ident $binders* : $stmtT := by pt_unproved)
        else `(@[pt_proof] theorem $n:ident $binders* : $stmtT := by pt_unproved)
      | none =>
        let n ← anonName stx
        if relaxed then `(@[pt_proof, pt_relaxed, pt_anon] theorem $n:ident $binders* : $stmtT := by pt_unproved)
        else `(@[pt_proof, pt_anon] theorem $n:ident $binders* : $stmtT := by pt_unproved)
    taggingProof.set true
    try elabCommand (← `(set_option autoImplicit false in set_option linter.unusedVariables false in
      set_option warn.sorry false in open PT in $cmd:command))
    finally taggingProof.set false
    return
  let mut lhs := first
  let mut chain : Option (Term × Bool) := none
  for st in steps do
    let isEq := st.getKind == ``ptStepEq
    let raw := st[2][0].getAtomVal
    let hintTxt := raw.trimAscii.toString
    -- Preserve hint positions for hover and go-to-definition.

    let lead := (raw.toList.takeWhile Char.isWhitespace).length
    let info := match st[2][0].getPos? with
      | some p => SourceInfo.synthetic ⟨p.byteIdx + lead⟩ ⟨p.byteIdx + lead + hintTxt.utf8ByteSize⟩ true
      | none => SourceInfo.none
    let hintLit : TSyntax `str := ⟨Syntax.mkStrLit hintTxt info⟩
    let rhs : TSyntax `ptf := ⟨st[4]⟩

    let a := Syntax.mkNumLit (toString ((st.getPos?.map (·.byteIdx)).getD 0))
    let b := Syntax.mkNumLit (toString ((st.getTailPos?.map (·.byteIdx)).getD 0))
    let (stepTy, pf) ← withRef st do
      let stepTy ← if isEq then `(pt_step% $lhs $rhs) else `(PT.Imp ⟪$lhs⟫ ⟪$rhs⟫)
      let pf ← `((by pt_step $hintLit $a $b : $stepTy))
      pure (stepTy, pf)
    chain := some (← match chain with
      | none => pure (pf, isEq)
      | some (c, cEq) => do
        pure (← withRef st `(pt_trans% $c $pf), cEq && isEq))
    lhs := rhs
  let some (chainTerm, _) := chain | throwError "empty proof"
  let stmtT ← `(⟪$stmt⟫)

  let assumeT ← assumptions.mapM fun a => `(⟪$a⟫)
  if !assumptions.isEmpty && stmt.raw.getKind != ``ptImp then
    throwErrorAt stx[5] "`assume` needs a statement of the form `A ⇒ B`. If `B` is an equation, bracket it, `A ⇒ (B = C)`, since `=` binds looser than `⇒`"
  let qa := Syntax.mkNumLit (toString ((stx[8].getPos?.map (·.byteIdx)).getD 0))
  let qb := Syntax.mkNumLit (toString ((stx[8].getTailPos?.map (·.byteIdx)).getD 0))
  let body ← withRef stx[8] <|
    if assumptions.isEmpty then `(by pt_conclude $qa $qb $chainTerm)
    else `(by pt_assume [$assumeT,*]; pt_conclude $qa $qb $chainTerm)

  if let some n := name? then
    let fullName := (← getCurrNamespace) ++ n.getId
    let ob := fullName ++ `ob
    if (← getEnv).contains ob then
      let some stName := stName? | throwError "no `state` declared"
      let ok ← liftTermElabM do
        Term.withAutoBoundImplicit <| Meta.withLocalDeclD `σ (mkConst stName) fun σ => do
          let e ← Term.elabTerm (← `(⟪$stmt⟫)) (some (mkSort .zero))
          Term.synthesizeSyntheticMVarsNoPostponing
          let e ← instantiateMVars e

          if ← (try Meta.isDefEq e (mkApp (mkConst ob) σ) catch _ => pure false) then return true
          let some v := ((← getEnv).find? ob).bind (·.value?) | return false
          return acNorm e == acNorm (← Meta.instantiateLambda v #[σ])
      unless ok do
        throwErrorAt stx[4] "this is not the obligation `{fullName}` of `program`"
  let cmd ← match name? with
    | some n =>
      if relaxed then `(@[pt_proof, pt_relaxed] theorem $n:ident $binders* : $stmtT := $body)
      else `(@[pt_proof] theorem $n:ident $binders* : $stmtT := $body)
    | none =>
      let n ← anonName stx
      if relaxed then `(@[pt_proof, pt_relaxed, pt_anon] theorem $n:ident $binders* : $stmtT := $body)
      else `(@[pt_proof, pt_anon] theorem $n:ident $binders* : $stmtT := $body)

  let assumed := Syntax.mkStrLit ("\u0001".intercalate (assumptions.toList.map fun a =>
    (a.raw.getSubstring?.map (·.toString.trimAscii.toString)).getD ""))
  taggingProof.set true
  try
    elabCommand (← `(set_option autoImplicit false in set_option linter.unusedVariables false in
      set_option maxHeartbeats 2000000 in set_option warn.sorry false in set_option pt.assumed $assumed in
      open PT in $cmd:command))
  finally taggingProof.set false

syntax (name := expectCmd) "expect " ident (num <|> scientific)? (ptBinder)* (" : " ptf)? : command

@[command_elab expectCmd] def elabExpect : CommandElab := fun stx => do
  if stx.hasMissing then return
  let name ← resolveProofRef stx[1]
  let pts := if stx[2].getNumArgs > 0 then
      (stx[2][0].getSubstring?.map (·.toString.trimAscii.toString)).getD "" else ""
  let report (s : String) : CommandElabM Unit := logInfo m!"{name}: {s}"
  let env ← getEnv
  if pt.tests.get (← getOptions) then logWarning m!"{name}: pt.tests is set, `#guard_msgs` may hide messages"
  let broken ← strictScan
  unless broken.isEmpty do logWarning m!"{name}: not in strict mode ({broken.size} places, see `status`), the report may be incomplete"
  if let some issue := (← checkProof name).issue? then
    report s!"{issue} (0 of {pts} pts)"; return
  let some ci := env.find? name | return
  if stx[4].getNumArgs > 0 then
    let binders ← headerBinders stx[3].getArgs
    let expected ← liftTermElabM <| Term.withAutoBoundImplicit <| Term.elabBinders binders fun xs => do
      let stmt : TSyntax `ptf := ⟨stripParens (← reassoc stx[4][1])⟩
      let e ← Term.elabTerm (← `(⟪$stmt⟫)) (some (mkSort .zero))
      Term.synthesizeSyntheticMVarsNoPostponing
      Meta.mkForallFVars xs (← instantiateMVars e)
    unless ← liftTermElabM (Meta.isDefEq expected ci.type) do
      report s!"proved a different statement (0 of {pts} pts)"; return
    report s!"proved ({pts} pts)"
  else

    let shown ← liftTermElabM <| Meta.forallTelescope ci.type fun _ body => do
      pure (toString (← Meta.ppExpr body))
    report s!"proved ({pts} pts), the statement is {shown}"

end PT
