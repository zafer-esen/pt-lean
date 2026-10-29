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

/-- `acNorm` under binders, with `≠`, `>`, `≥` unfolded and the sides of `=` ordered. -/
partial def acNormDeep (e : Expr) : Expr :=
  let e := e.consumeMData
  match e with
  | .lam n t b bi => .lam n t (acNormDeep b) bi
  | .forallE n t b bi => .forallE n t (acNormDeep b) bi
  | .app .. =>
    let args := e.getAppArgs
    let f := e.getAppFn
    if e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 then
      let op := if e.isAppOfArity ``And 2 then ``And else ``Or
      let ops := ((leaves op e).map acNormDeep).qsort (fun a b => Expr.lt a b)
      ops.pop.foldr (fun x acc => mkApp2 (mkConst op) x acc) ops.back!
    else if e.isAppOfArity ``Iff 2 || e.isAppOfArity ``Eq 3 then
      let n := args.size
      let a := acNormDeep args[n - 2]!
      let b := acNormDeep args[n - 1]!
      let (a, b) := if Expr.lt a b then (a, b) else (b, a)
      mkAppN f (args.extract 0 (n - 2) ++ #[a, b])
    else if let some r := unfoldRelation? e then acNormDeep r
    else mkAppN (acNormDeep f) (args.map acNormDeep)
  | _ => e

/-- Each integer term in its linear normal form, e.g., `r + 1 - y - 1` as `r - y`. Relations are kept as written. -/
def linearTerms (e : Expr) : MetaM Expr := do
  let ctx ← Meta.Simp.mkContext { arith := true } #[] (← Meta.getSimpCongrTheorems)
  Meta.transform e (pre := fun t => do
    let intOp := (t.isAppOfArity ``HAdd.hAdd 6 || t.isAppOfArity ``HSub.hSub 6 || t.isAppOfArity ``HMul.hMul 6 ||
      t.isAppOfArity ``Neg.neg 3) && (t.getArg! 0).isConstOf ``Int
    if intOp then return .done (← Meta.simp t ctx).1.expr
    return .continue)

/-- Equal up to order, grouping and linear integer arithmetic in terms. -/
def sameFormula (a b : Expr) : MetaM Bool := do
  if ← (try Meta.isDefEq a b catch _ => pure false) then return true
  let norm (e : Expr) : MetaM Expr := do
    let e ← instantiateMVars e
    let e ← try pure (← intNormalize e).expr catch _ => pure e
    let e ← try linearTerms e catch _ => pure e
    return acNormDeep e
  return (← norm a) == (← norm b)

/-- Roles of the parts of a program obligation. -/
structure ObRoles where
  template : String
  ante : Array String
  cons : String := ""
  cmdSym : String := ""
  postSym : String := ""
  /-- What a symbol stands for when the student writes the program's own expression. -/
  note : String := ""
  /-- The command, `program` or `proc`, that the obligation belongs to. -/
  owner : String := "program"
  deriving Inhabited

initialize obRolesExt : EnvExtension (NameMap ObRoles) ← registerEnvExtension (pure {})

/-- The antecedent `A₁ ∧ … ∧ Aₖ` of an obligation with `k` roles. -/
private def anteParts : Nat → Expr → Array Expr
  | k + 2, e => match e.app2? ``And with
    | some (x, y) => #[x] ++ anteParts (k + 1) y
    | none => #[e]
  | _, e => #[e]

/-- Say which part of statement `e` differs from obligation `n`, without showing the obligation. -/
def diagnoseObligation (n : Name) (e σ : Expr) : MetaM (Option String) := do
  let env ← getEnv
  let roles? := (obRolesExt.getState env).find? n
  let some roles := roles? | return none
  let some v := (env.find? (n ++ `ob)).bind (·.value?) | return none
  let ob ← Meta.instantiateLambda v #[σ]
  let some (oa, oc) := ob.app2? ``PT.Imp | return none
  let parts := anteParts roles.ante.size oa
  let e ← instantiateMVars e
  let some (sa, sc) := e.app2? ``PT.Imp | do
    let lhs := (e.iff?.map (·.1)) <|> (e.eq?.map (·.2.1))
    if lhs.any (·.isAppOfArity ``PT.Imp 2) then
      return some "bracket its consequent, since `=` binds looser than `⇒`"
    return some "it is not an implication"
  if parts.size ≥ 2 && sc.isAppOfArity ``PT.Imp 2 && !sa.isAppOfArity ``And 2 then
    return some "write its antecedent as one conjunction"
  let sLeaves := leaves ``And sa
  let mut used := sLeaves.map fun _ => false
  for p in parts, role in roles.ante do
    for l in leaves ``And p do
      match ← sLeaves.findIdxM? (sameFormula · l) with
      | some j => used := used.set! j true
      | none => return some s!"its antecedent is missing {role}"
  -- An extra part may belong to another obligation of the program.
  let siblings := (obRolesExt.getState env).toList.filter fun (m, _) => m.getPrefix == n.getPrefix && m != n
  for l in sLeaves, u in used do
    if u then continue
    for (m, r) in siblings do
      let some w := (env.find? (m ++ `ob)).bind (·.value?) | continue
      let some (ma, _) := (← Meta.instantiateLambda w #[σ]).app2? ``PT.Imp | continue
      let mparts := anteParts r.ante.size ma
      for mp in mparts, role in r.ante do
        if (← (leaves ``And mp).anyM (sameFormula · l)) && !roles.ante.contains role then
          return some s!"its antecedent has {role}, which belongs to another obligation"
    return some s!"its antecedent has a part that is not {" or ".intercalate roles.ante.toList}"
  if roles.cmdSym != "" then
    let expectWp := s!"its consequent is not wp({roles.cmdSym}, {roles.postSym})"
    unless sc.isAppOfArity ``PT.wp 4 && oc.isAppOfArity ``PT.wp 4 do return some expectWp
    unless ← sameFormula (sc.getArg! 1) (oc.getArg! 1) do
      return some s!"inside wp, the command is not {roles.cmdSym} as written in the program"
    unless ← sameFormula ((sc.getArg! 2).beta #[σ]) ((oc.getArg! 2).beta #[σ]) do
      return some s!"inside wp, the postcondition is not {roles.postSym}"
  else
    unless ← sameFormula sc oc do return some s!"its consequent is not {roles.cons}"
  return none

/-- Compare with `n.ob` by `sameFormula`. Accept if no obligation exists. -/
def statesObligation (n : Name) : CommandElabM Bool := do
  let env ← getEnv
  let some ci := env.find? n | return false
  let some ob := env.find? (n ++ `ob) | return true
  liftTermElabM do
    let .forallE _ St _ _ := ob.type | return false
    Meta.withLocalDeclD `σ St fun σ => do
      let a ← Meta.instantiateForall ci.type #[σ]
      let some v := ob.value? | return false
      sameFormula a (← Meta.instantiateLambda v #[σ])

/-- Obligation proofs rejected for their statement, reported by `verified` instead of "missing". -/
initialize rejectedExt : EnvExtension (Array Name) ← registerEnvExtension (pure #[])

/-- Names of the obligations generated by `program` and `proc`. -/
def isObligationName (s : String) : Bool :=
  let base := String.ofList (s.toList.takeWhile Char.isAlpha)
  let num := String.ofList (s.toList.dropWhile Char.isAlpha)
  (num.isEmpty || num.isNat) &&
    (["inv", "dec", "branch", "before", "after"].contains base ||
      (num.isEmpty && ["init", "post", "bound", "guards", "body"].contains base))

/-- Every `program` and `proc` has one of these obligations. -/
def firstObligations : List Name := [`init, `guards, `before, `body]

def noProgramMessage (name : Name) : String :=
  s!"there is no `program {name}` or `proc {name}` without errors"

structure ProofCheck where
  owner : String := "program"
  rejected : Bool := false
  present : Bool := false
  block : Bool := false
  complete : Bool := false
  axiomatic : Bool := false
  relaxed : Bool := false
  matchesObligation : Bool := true

def ProofCheck.issue? (c : ProofCheck) : Option String :=
  if !c.present then some (if c.rejected then "its statement is not the obligation" else "missing")
  else if !c.block then some "not a proof block"
  else if !c.complete then some "not proved"
  else if c.axiomatic then some "rests on an axiom of the file"
  else if c.relaxed then some "checked with weakened options"
  else if !c.matchesObligation then some s!"its statement is not the obligation of `{c.owner}`"
  else none

def checkProof (n : Name) : CommandElabM ProofCheck := do
  let env ← getEnv
  let some ci := env.find? n | return { rejected := (rejectedExt.getState env).contains n }
  unless ci.isTheorem do return { present := true }
  let axioms ← liftCoreM (collectAxioms n)
  return {
    owner := ((obRolesExt.getState env).find? n).elim "program" (·.owner)
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

  let declName? := name?.map ((← getCurrNamespace) ++ ·.getId)
  let asProof {α} (x : TermElabM α) : TermElabM α := match declName? with
    | some n => Term.withDeclName n x
    | none => x
  let stmt : TSyntax `ptf ← liftTermElabM <| asProof <| Term.withAutoBoundImplicit <|
    Term.elabBinders binders fun _ => do pure ⟨← reassoc stx[4]⟩
  let stmt : TSyntax `ptf := ⟨stripParens stmt⟩
  let assumptions : Array (TSyntax `ptf) :=
    if stx[5].getNumArgs > 0 then stx[5][0][1].getSepArgs.map (⟨·⟩) else #[]
  if let some n := name? then
    let fullName := (← getCurrNamespace) ++ n.getId
    let ob := fullName ++ `ob
    if (← getEnv).contains ob then
      let some stName := stName? | throwError "no `state` declared"
      let (ok, why) ← liftTermElabM <| asProof do
        Term.withAutoBoundImplicit <| Meta.withLocalDeclD `σ (mkConst stName) fun σ => do
          let e ← Term.elabTerm (← `(⟪$stmt⟫)) (some (mkSort .zero))
          Term.synthesizeSyntheticMVarsNoPostponing
          let e ← instantiateMVars e
          let some v := ((← getEnv).find? ob).bind (·.value?) | return (false, none)
          if ← sameFormula e (← Meta.instantiateLambda v #[σ]) then return (true, none)
          return (false, ← diagnoseObligation fullName e σ)
      unless ok do
        modifyEnv (rejectedExt.modifyState · (·.push fullName))
        let roles := (obRolesExt.getState (← getEnv)).find? fullName
        let why := why.map (s!", " ++ ·) |>.getD ""
        let form := roles.map (s!". It has the form " ++ ·.template) |>.getD ""
        let note := roles.filter (·.note != "") |>.map (s!", where " ++ ·.note) |>.getD ""
        let owner := roles.elim "program" (·.owner)
        throwErrorAt stx[4] "this is not the obligation `{fullName}` of `{owner} {fullName.getPrefix}`{why}{form}{note}"
    else if n.getId.getNumParts > 1 && isObligationName n.getId.getString! then
      let prog := fullName.getPrefix
      let env ← getEnv
      let isProgram := firstObligations.any fun ob => env.contains (prog ++ ob ++ `ob)
      logWarningAt n (if isProgram then
          m!"`{prog}` has no obligation `{n.getId.getString!}`, so this is checked as an ordinary proof"
        else m!"{noProgramMessage prog}, so this is checked as an ordinary proof")
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
    if !isEq && pt.equalityOnly.get (← getOptions) then
      throwErrorAt st[0] "`⇒` steps are disabled. Use only `=` steps in calculations"
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
    unless ← liftTermElabM (sameFormula expected ci.type) do
      report s!"proved a different statement (0 of {pts} pts)"; return
    report s!"proved ({pts} pts)"
  else

    let shown ← liftTermElabM <| Meta.forallTelescope ci.type fun _ body => do
      pure (toString (← Meta.ppExpr body))
    report s!"proved ({pts} pts), the statement is {shown}"

end PT
