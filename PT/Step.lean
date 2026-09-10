import Lean
import PT.Hints

open Lean Elab Tactic Meta Command

namespace PT

/-! ## Instances of theorems -/

/-- Generalize only the state fields mentioned in the lemma. -/
def schematicState (σ : LocalDecl) (body : Expr) : MetaM Expr := do
  let env ← getEnv
  let σe := mkFVar σ.fvarId
  let some st := σ.type.constName? | return σe
  let some info := getStructureInfo? env st | return σe
  let body := body.instantiate1 σe
  let mut args := #[]
  let mut any := false
  for f in info.fieldNames do
    let some proj := getProjFnForField? env st f | return σe
    let field := mkApp (mkConst proj) σe
    if (body.find? (· == field)).isSome then
      any := true
      args := args.push (← mkFreshExprMVar (← inferType field))
    else args := args.push field
  unless any do return σe
  return mkAppN (mkConst (getStructureCtor env st).name) args

def reduceFields (e : Expr) : MetaM Expr := do
  let env ← getEnv
  Meta.transform e (post := fun e => do
    let .const n _ := e.getAppFn | return .done e
    let some info := env.getProjectionFnInfo? n | return .done e
    unless e.getAppNumArgs == info.numParams + 1 do return .done e
    let some (.ctorInfo _) := e.appArg!.getAppFn.constName?.bind env.find? | return .done e
    return .done (← whnfR e))

def lawApp (e : Expr) (args : Array Expr) (ty : Expr) : MetaM Expr := do
  let e := mkAppN e args
  if (← instantiateMVars (← inferType e)) == ty then return e
  mkExpectedTypeHint e ty

/-- Instantiate a theorem with metavariables. State-independent variables must be
created outside `σ` so predicates can match formulas containing state fields. -/
def lawTelescope (e : Expr) : MetaM (Array Expr × Expr) := do
  let lctx ← getLCtx
  let σ? := lctx.findFromUserName? `σ
  let mut e := e
  let mut ty ← instantiateMVars (← inferType e)
  let mut args := #[]
  let mut schematic := false
  while ty.isForall do
    let d := ty.bindingDomain!
    let a ← match σ? with
      | some σ =>
        if ← isDefEq d σ.type then
          let a ← schematicState σ ty.bindingBody!
          unless a.isFVar do schematic := true
          pure a
        else
          let dW ← whnf d
          let overState ← pure dW.isForall <&&> isDefEq dW.bindingDomain! σ.type
          if overState && !d.containsFVar σ.fvarId then
            withLCtx (lctx.erase σ.fvarId) (← getLocalInstances) (mkFreshExprMVar d)
          else mkFreshExprMVar d
      | none => mkFreshExprMVar d
    args := args.push a
    e := mkApp e a
    ty := ty.bindingBody!.instantiate1 a
  ty ← instantiateMVars ty
  if schematic then ty ← reduceFields ty
  return (args, ty)

/-- Instantiate the theorem, turning implication premises into side conditions. -/
def instantiateLaw (c : Name) : MetaM (Expr × Expr) := do
  let e ← mkConstWithFreshMVarLevels c
  let (args, ty) ← lawTelescope e
  let mut e ← lawApp e args ty
  let mut ty := ty
  if let some (cnd, body) := ty.app2? ``PT.Imp then
    if body.isAppOfArity ``Iff 2 || body.isAppOfArity ``Eq 3 then
      e := mkApp e (← mkFreshExprMVar cnd)
      ty := body
  return (e, ty)

def hasCondition (c : Name) : MetaM Bool := do
  let some ci := (← getEnv).find? c | return false
  forallTelescope ci.type fun xs body => do
    for x in xs do
      if ← isProp (← inferType x) then return true
    return body.isAppOfArity ``PT.Imp 2 &&
      ((body.getArg! 1).isAppOfArity ``Iff 2 || (body.getArg! 1).isAppOfArity ``Eq 3)

def assignState (m : MVarId) : MetaM Bool := do
  let some d := (← getLCtx).findFromUserName? `σ | return false
  if ← isDefEq (← m.getType) d.type then
    m.assign (mkFVar d.fvarId); return true
  return false

private def commSide (side : Expr) : Option (Expr × Expr) :=
  if let some (a, b) := side.app2? ``And then
    some (mkApp2 (mkConst ``And) b a, mkApp2 (mkConst ``PT.Commutativity.and) b a)
  else if let some (a, b) := side.app2? ``Or then
    some (mkApp2 (mkConst ``Or) b a, mkApp2 (mkConst ``PT.Commutativity.or) b a)
  else if let some (a, b) := side.iff? then
    some (mkApp2 (mkConst ``Iff) b a, mkApp2 (mkConst ``PT.Commutativity.eq) b a)
  else none

private def nestedComm (side : Expr) : MetaM (Array (Expr × Expr)) := do
  if let some a := side.app1? ``Not then
    if let some (a', ha) := commSide a then
      return #[(mkApp (mkConst ``Not) a', ← mkAppM ``not_congr #[ha])]
    return #[]
  let some (op, a, b) :=
      (match side.app2? ``And with
       | some (a, b) => some (``And, a, b)
       | none => match side.app2? ``Or with
         | some (a, b) => some (``Or, a, b)
         | none => match side.iff? with
           | some (a, b) => some (``Iff, a, b)
           | none => none)
    | return #[]
  let congr := if op == ``And then ``and_congr else if op == ``Or then ``or_congr else ``iff_congr
  let mut out := #[]
  if let some (a', ha) := commSide a then
    out := out.push (mkApp2 (mkConst op) a' b, ← mkAppM congr #[ha, ← mkAppM ``Iff.refl #[b]])
  if let some (b', hb) := commSide b then
    out := out.push (mkApp2 (mkConst op) a b', ← mkAppM congr #[← mkAppM ``Iff.refl #[a], hb])
  return out

/-- Commute operands at the top or one level down. -/
def acVariants (e ty : Expr) : MetaM (Array Expr) := do
  let some (l, r) := ty.iff? | return #[e]
  let mut base := #[e]
  if let some (l', hl) := commSide l then
    base := base.push (mkApp5 (mkConst ``Iff.trans) l' l r hl e)
  if let some (r', hr) := commSide r then
    base := base.push (mkApp5 (mkConst ``Iff.trans) l r r' e (mkApp3 (mkConst ``Iff.symm) r' r hr))
  if let some (l', hl) := commSide l then
    if let some (r', hr) := commSide r then
      let e1 := mkApp5 (mkConst ``Iff.trans) l' l r hl e
      base := base.push (mkApp5 (mkConst ``Iff.trans) l' r r' e1 (mkApp3 (mkConst ``Iff.symm) r' r hr))
  let mut out := base
  for v in base do
    let some (lv, rv) := (← inferType v).iff? | continue
    let ls ← nestedComm lv
    for (_, hl) in ls do
      out := out.push (← mkAppM ``Iff.trans #[hl, v])

    if h : ls.size = 2 then
      let (l1, h1) := ls[0]
      for (_, h2) in ← nestedComm l1 do
        if (← inferType h2).iff?.any fun (x, _) => x != lv then
          out := out.push (← mkAppM ``Iff.trans #[← mkAppM ``Iff.trans #[h2, h1], v])
    let rs ← nestedComm rv
    for (_, hr) in rs do
      out := out.push (← mkAppM ``Iff.trans #[v, ← mkAppM ``Iff.symm #[hr]])
    if h : rs.size = 2 then
      let (r1, h1) := rs[0]
      for (_, h2) in ← nestedComm r1 do
        if (← inferType h2).iff?.any fun (x, _) => x != rv then
          out := out.push (← mkAppM ``Iff.trans #[v, ← mkAppM ``Iff.symm #[← mkAppM ``Iff.trans #[h2, h1]]])
  return out

def impVariants (e ty : Expr) : MetaM (Array Expr) := do
  let some (l, r) := ty.app2? ``PT.Imp | return #[e]
  let mut out := #[e]
  if let some (l', hl) := commSide l then
    out := out.push (mkApp5 (mkConst ``PT.step_ei) l' l r hl e)
  if let some (r', hr) := commSide r then
    out := out.push (mkApp5 (mkConst ``PT.step_ie) l r r' e (mkApp3 (mkConst ``Iff.symm) r' r hr))
  if let some (l', hl) := commSide l then
    if let some (r', hr) := commSide r then
      let e1 := mkApp5 (mkConst ``PT.step_ei) l' l r hl e
      out := out.push (mkApp5 (mkConst ``PT.step_ie) l' r r' e1 (mkApp3 (mkConst ``Iff.symm) r' r hr))
  return out

/-! ## Closing a goal -/

syntax "pt_ac" : tactic
macro_rules
  | `(tactic| pt_ac) => `(tactic| first
      | (refine Iff.of_eq ?_; simp only [and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc, iff_comm]; done)
      | (refine PT.Imp.of_eq ?_; simp only [and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc, iff_comm]; done)
      | (simp only [and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc, iff_comm]; done))

def focusMain (tac : TacticM Unit) : TacticM Bool := do
  let s ← saveState
  let g :: rest ← getGoals | return false
  try
    setGoals [g]
    tac
    if (← getUnsolvedGoals).isEmpty then
      setGoals rest
      return true
    s.restore
    return false
  catch _ =>
    s.restore
    return false

def closeByRfl : TacticM Bool :=
  focusMain do evalTactic (← `(tactic| with_reducible rfl))

/-- Detect conditions discharged from the surrounding formula. -/
def usesLineHyp (pf : Expr) : MetaM Bool := do
  let lctx ← getLCtx
  return pf.hasAnyFVar fun f => match lctx.find? f with
    | some d => let s := d.userName.eraseMacroScopes.toString; s == "h" || s.startsWith "h_"
    | none => false

def stepSides (ty : Expr) : Option (Expr × Expr) :=
  match ty.iff? with
  | some (a, b) => some (a, b)
  | none => match ty.app2? ``PT.Imp with
    | some (a, b) => some (a, b)
    | none => match ty.eq? with
      | some (_, a, b) => some (a, b)
      | none => none

/-- The tactic can prove more than the implicit laws. Limit it with this AC normal form. -/
partial def acNorm (e : Expr) : Expr :=
  let cluster (op : Name) : Option (Array Expr) :=
    if e.isAppOfArity op 2 then
      let rec flat (e : Expr) : Array Expr :=
        match e.app2? op with
        | some (a, b) => flat a ++ flat b
        | none => #[e]
      some (flat e)
    else none
  match cluster ``And <|> cluster ``Or with
  | some ops =>
    let op := if e.isAppOfArity ``And 2 then ``And else ``Or
    let ops := (ops.map acNorm).qsort (fun a b => Expr.lt a b)
    ops.foldr (init := none) (fun x acc => match acc with
      | none => some x
      | some a => some (mkApp2 (mkConst op) x a)) |>.get!
  | none =>
    match e.iff? with
    | some (a, b) =>
      let a := acNorm a
      let b := acNorm b
      if Expr.lt a b then mkApp2 (mkConst ``Iff) a b else mkApp2 (mkConst ``Iff) b a
    | none =>
      match e with
      | .app f a => .app (acNorm f) (acNorm a)
      | .mdata _ b => acNorm b
      | _ => e

def goalIsACEqual : TacticM Bool := do
  let some (a, b) := stepSides (← instantiateMVars (← getMainTarget)) | return false
  return acNorm a == acNorm b

def closeByAC : TacticM Bool := do
  unless ← goalIsACEqual do return false
  focusMain do evalTactic (← `(tactic| pt_ac))

def intNormalize (e : Expr) : MetaM Simp.Result := do
  let mut thms : SimpTheorems := {}
  for n in [``Int.add_sub_cancel, ``Int.sub_add_cancel, ``Int.add_zero, ``Int.zero_add, ``Int.sub_zero,
      ``Int.sub_self, ``Int.add_sub_assoc, ``Int.add_neg_cancel_right, ``Int.neg_add_cancel_right] do
    thms ← thms.addConst n
  let mut procs : Simprocs := {}
  for n in [``Int.reduceAdd, ``Int.reduceSub, ``Int.reduceMul, ``Int.reduceNeg] do
    procs ← procs.add n (post := true)
  let ctx ← Simp.mkContext {} #[thms] (← getSimpCongrTheorems)
  let (r, _) ← simp e ctx #[procs]
  return r

def hasArith (e : Expr) : Bool :=
  (e.find? fun c => c.isConstOf ``Int || c.isConstOf ``PT.odd || c.isConstOf ``PT.even).isSome

def closeStep (arith : Bool := true) : TacticM Bool := do
  if (← getGoals).isEmpty then return true
  if ← closeByRfl then return true
  if ← closeByAC then return true
  unless arith do return false
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  unless hasArith ty do return false
  let some (a, b) := stepSides ty | return false
  let s ← saveState
  try
    let ra ← intNormalize a
    let rb ← intNormalize b
    unless acNorm ra.expr == acNorm rb.expr do throwError "not equal"

    let ty' ← if ty.isAppOfArity ``Eq 3 then mkEq ra.expr rb.expr
      else pure (mkApp2 (mkConst ``Iff) ra.expr rb.expr)
    let g' ← mkFreshExprSyntheticOpaqueMVar ty'
    let pa ← ra.getProof
    let pb ← rb.getProof
    let pf ← if ty.isAppOfArity ``Eq 3 then
        mkAppM ``Eq.trans #[pa, ← mkAppM ``Eq.trans #[g', ← mkEqSymm pb]]
      else
        let h ← mkAppM ``Iff.trans #[← mkAppM ``Iff.of_eq #[pa], ← mkAppM ``Iff.trans #[g', ← mkAppM ``Iff.of_eq #[← mkEqSymm pb]]]
        if ty.isAppOfArity ``PT.Imp 2 then mkAppM ``PT.Imp.of_iff #[h] else pure h
    goal.assign pf
    setGoals [g'.mvarId!]
    if ← closeByRfl then return true
    if ← closeByAC then return true
    throwError "not closed"
  catch _ =>
    s.restore
    return false

def arithScript : TacticM Unit := do
  -- Absorb generated `True` and preserve explicit `T` and `F`.

  let written := ((← getMainTarget).find? fun e => e.isConstOf ``PT.T || e.isConstOf ``PT.F).isSome
  if written then
    evalTactic (← `(tactic| (try simp only [PT.T_def, PT.F_def, PT.Imp_def, PT.even_def, PT.odd_def,
        eq_self_iff_true, ite_true, ite_false, iff_true, true_iff, iff_false, false_iff, implies_true,
        true_implies, false_implies, not_true_eq_false, not_false_eq_true, Int.pow_succ,
        Int.pow_zero, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.one_mul, Int.mul_one,
        Int.zero_mul, Int.mul_zero, Int.mul_comm] at *) <;>
      first | omega | (constructor <;> intro _ <;> omega) | (split <;> omega)
            | simp +arith only [ne_eq, eq_self_iff_true, not_true_eq_false, not_false_eq_true]
            | (intros; simp_all only [Int.mul_zero, Int.zero_mul]; first | done | omega)))
  else
    evalTactic (← `(tactic| (try simp only [PT.T_def, PT.F_def, PT.Imp_def, PT.even_def, PT.odd_def,
        eq_self_iff_true, ite_true, ite_false, iff_true, true_iff, iff_false, false_iff, implies_true,
        true_implies, false_implies, and_true, true_and, and_false, false_and, or_true, true_or,
        or_false, false_or, not_true_eq_false, not_false_eq_true, Int.pow_succ,
        Int.pow_zero, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.one_mul, Int.mul_one,
        Int.zero_mul, Int.mul_zero, Int.mul_comm] at *) <;>
      first | omega | (constructor <;> intro _ <;> omega) | (split <;> omega)
            | simp +arith only [ne_eq, eq_self_iff_true, not_true_eq_false, not_false_eq_true]
            | (intros; simp_all only [Int.mul_zero, Int.zero_mul]; first | done | omega)))

def closedArith (m : MVarId) : TacticM Bool := do
  let gs ← getGoals
  let s ← saveState
  try
    let mut m := m
    for d in ← m.withContext getLCtx do
      if d.isImplementationDetail then continue
      if ← m.withContext (isProp d.type) then m ← m.tryClear d.fvarId
    setGoals [m]
    evalTactic (← `(tactic| intros))
    if (← getUnsolvedGoals).isEmpty then setGoals gs; return true

    unless hasArith (← getMainTarget) do
      evalTactic (← `(tactic| (simp only [PT.T_def, PT.F_def, not_false_eq_true, not_true_eq_false, and_true,
        true_and, or_true, true_or]; try trivial)))
      if (← getUnsolvedGoals).isEmpty then setGoals gs; return true
      throwError "not arithmetic"
    arithScript
    if (← getUnsolvedGoals).isEmpty then setGoals gs; return true
  catch _ => pure ()
  s.restore
  return false

/-- Discharge a condition from cited hypotheses, closed arithmetic, or helper proofs.
Restore the goal list afterwards. -/
def closeCondition (m : MVarId) (helpers : Array Name := #[]) : TacticM Bool := do
  let gs ← getGoals
  let s ← saveState

  if ← focusOn m (evalTactic (← `(tactic| assumption))) then return true
  try
    setGoals [m]
    evalTactic (← `(tactic| and_intros))
    for g in ← getGoals do
      let mut ok ← focusOn g (evalTactic (← `(tactic| assumption)))
      unless ok do ok ← closedArith g
      for h in helpers do
        if ok then break
        let hh := mkIdent h
        ok ← focusOn g (evalTactic (← `(tactic| (apply $hh <;> assumption))))
      unless ok do throwError "condition not closed"
    setGoals gs
    return true
  catch _ =>
    s.restore
    return false
where
  focusOn (g : MVarId) (tac : TacticM Unit) : TacticM Bool := do
    let s ← saveState
    let gs ← getGoals
    try
      setGoals [g]
      tac
      if (← getUnsolvedGoals).isEmpty then setGoals gs; return true
    catch _ => pure ()
    s.restore
    return false

/-! ## One rewrite of the left side -/

inductive FailKind

  | noMatch
  /-- `assumed` means an uncited hypothesis suffices. `matched` means the remaining step succeeds. -/
  | condition (c : Expr) (assumed matched : Bool)

  | open_
  /-- Record the result, direction, and whether a side condition also failed. -/
  | mismatch (descr : MessageData) (result : Expr) (back failed : Bool)

  | noPosition

structure Fail where
  line : Expr
  next : Expr
  kind : FailKind

  flipped : Bool := false

def FailKind.rank : FailKind → Nat
  | .condition _ _ true => 7
  | .condition _ true _ => 6
  | .mismatch _ _ false false => 5
  | .condition .. | .mismatch _ _ false true => 4
  | .open_ => 3
  | .noMatch | .noPosition => 2
  -- a theorem read from right to left fits many lines, and rarely tells anything
  | .mismatch _ _ true _ => 1

def Fail.better (f : Fail) : Option Fail → Fail
  | none => f
  | some g => if f.kind.rank > g.kind.rank then f else g

/-- Scope and condition sources for Conditional Substitution. -/
structure Scope where
  cited : Array FVarId

  helpers : Array Name := #[]
  usedHyp : IO.Ref Bool
  closable : Expr → TacticM Bool

/-- Rewrite the selected occurrences, prove all conditions, and infer all variables. -/
def rewriteLeft (heq : Expr) (symm : Bool) (occs : Occurrences) (sc : Scope) : TacticM (Option FailKind) := do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some (a, b) := stepSides ty | return some .noMatch
  let r ← try goal.rewrite a heq symm { occs } catch _ => return some .noMatch
  let a' := r.eNew
  let (g', pf) ← do
    if ty.isAppOfArity ``Iff 2 then
      let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Iff) a' b)
      pure (g', ← mkAppM ``Iff.trans #[← mkAppM ``Iff.of_eq #[r.eqProof], g'])
    else if ty.isAppOfArity ``PT.Imp 2 then
      let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``PT.Imp) a' b)
      pure (g', ← mkAppM ``PT.step_ei #[← mkAppM ``Iff.of_eq #[r.eqProof], g'])
    else
      let g' ← mkFreshExprSyntheticOpaqueMVar (← mkEq a' b)
      pure (g', ← mkAppM ``Eq.trans #[r.eqProof, g'])
  goal.assign pf
  replaceMainGoal [g'.mvarId!]
  for m in (← getMVars heq) ++ r.mvarIds.toArray do
    if ← m.isAssigned then continue
    if ← assignState m then continue
    let mty ← instantiateMVars (← m.getType)
    if ← isProp mty then
      unless ← closeCondition m sc.helpers do return some (.condition mty (← sc.closable mty) false)
      let pf ← instantiateMVars (mkMVar m)
      if pf.hasAnyFVar (sc.cited.contains ·) || pf.getUsedConstants.any sc.helpers.contains
          || (← usesLineHyp pf) then
        sc.usedHyp.set true
    else return some .open_
  return none

/-- Bare variables and constants take their instance from the next line. -/
def isBare (pat : Expr) : Bool :=
  pat.getAppFn.isMVar || pat.isConst

partial def subterms (e : Expr) : MetaM (Array Expr) := do
  let rec go (e : Expr) (acc : Array Expr) : MetaM (Array Expr) := do
    let acc ← do
      if e.hasLooseBVars || acc.contains e then pure acc
      else
        let ty? ← try some <$> inferType e catch _ => pure none
        match ty? with
        | some ty => if ty.isProp || ty.isConstOf ``Int then pure (acc.push e) else pure acc
        | none => pure acc
    match e with
    | .app f x => go x (← go f acc)
    | .mdata _ b => go b acc
    | .lam _ _ b _ => go b acc
    | .forallE _ _ b _ => go b acc
    | _ => return acc
  go e #[]

/-- Infer open variables by matching the result against the next line. -/
def fixFromNext (v res : Expr) (subsB : Array Expr) : TacticM Bool := do
  -- Variables absent from the theorem statement may be instantiated arbitrarily.

  let inStmt ← getMVars (← instantiateMVars (← inferType v))
  for m in ← getMVars v do
    if (← m.isAssigned) || inStmt.contains m then continue
    let mty ← instantiateMVars (← m.getType)
    if mty.isProp then m.assign (mkConst ``True)
    else if mty.isConstOf ``Int then m.assign (toExpr (0 : Int))
  let open_ ← (← getMVars v).filterM fun m => do
    return !(← m.isAssigned) && !(← isProp (← m.getType))
  if open_.isEmpty then return true
  let res ← instantiateMVars res
  let pieces := #[res] ++ (match res.app2? ``And with
    | some (x, y) => #[x, y]
    | none => match res.app2? ``Or with
      | some (x, y) => #[x, y]
      | none => #[])
  for piece in pieces do
    for w in subsB do
      let s ← saveState
      if ← isDefEq piece w then
        if ← open_.allM (·.isAssigned) then return true
      s.restore
  return false

/-! ## Schemas -/

private partial def replaceEApps (E : Expr) : Expr → StateT (Array (Expr × Expr)) MetaM Expr
  | .app f a => do
    if f == E then
      match (← get).find? (·.1 == a) with
      | some (_, x) => return x
      | none =>
        let x ← mkFreshExprMVar (mkSort Level.zero)
        modify (·.push (a, x))
        return x
    else return .app (← replaceEApps E f) (← replaceEApps E a)
  | .mdata _ b => replaceEApps E b
  | e => return e

/-- Infer the schema context by abstracting `t` from the matched formula. -/
def schemaInstance (v pat a t : Expr) : TacticM Bool := do
  let some E ← (← getMVars v).findM? (fun m => do return isContextType (← m.getType))
    | return false
  let E := mkMVar E
  let dom := (← inferType E).bindingDomain!
  let (shape, apps) ← (replaceEApps E pat).run #[]
  unless ← isDefEq shape a do return false
  for (arg, x) in apps do
    let arg ← instantiateMVars arg

    if arg.isMVar then
      unless ← isDefEq arg t do return false
    let arg ← instantiateMVars arg
    let s ← saveState
    try
      let x ← instantiateMVars x
      let body ← kabstract x arg
      unless body.hasLooseBVars do throwError "no occurrence"
      E.mvarId!.assign (mkLambda `z .default dom body)
      if ← withReducible (isDefEq (← instantiateMVars pat) a) then return true
    catch _ => pure ()
    s.restore
  return false

/-! ## Implication steps -/

def applyImp (v : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  let goalTy ← instantiateMVars (← goal.getType)
  let (args, ty) ← lawTelescope v
  unless ← withReducible (isDefEq ty goalTy) do throwError "does not apply"
  goal.assign (← instantiateMVars (mkAppN v args))
  let mut newGoals : List MVarId := []
  for a in args do
    let a ← instantiateMVars a
    if a.isMVar then
      if ← assignState a.mvarId! then continue
      if ← isProp (← inferType a) then newGoals := newGoals ++ [a.mvarId!]
      else if (← inferType a).isProp then continue
      else throwError "underdetermined"
  replaceMainGoal newGoals

/-- Apply an implication through a monotone position, preserving the other operands. -/
partial def monoApply (make : MetaM (Array Expr)) (fuel : Nat) (used : IO.Ref Bool) : TacticM Unit := do
  if fuel == 0 then throwError "too deep"
  let n := (← make).size
  unless ← used.get do
    for i in [0:n] do
      let s ← saveState
      try
        applyImp (← make)[i]!
        used.set true
        return
      catch _ => s.restore
  let open_ ← do
    let t ← instantiateMVars (← getMainTarget)
    pure (((t.app2? ``PT.Imp).map fun (_, r) => r.isMVar).getD false)
  unless open_ do
    if ← closeByRfl then return
    if ← closeByAC then return
  for lem in [``PT.Imp.and_mono, ``PT.Imp.or_mono, ``PT.Imp.not_anti, ``PT.Imp.imp_mono] do
    let s ← saveState
    try
      let before := (← getGoals).length
      applyImp (← mkConstWithFreshMVarLevels lem)
      let k := (← getGoals).length + 1 - before
      for _ in [0:k] do
        monoApply make (fuel - 1) used
      return
    catch _ => s.restore
  for lem in [``PT.Imp.and_left_ac, ``PT.Imp.and_right_ac, ``PT.Imp.or_left_ac, ``PT.Imp.or_right_ac] do
    let s ← saveState
    try
      applyImp (← mkConstWithFreshMVarLevels lem)
      monoApply make (fuel - 1) used
      if ← closeByRfl then return
      if ← closeByAC then return
      throwError "not equal up to AC"
    catch _ => s.restore
  throwError "no monotone position"

/-! ## Inside a formula -/

partial def andLeaves (pf ty : Expr) : Array (Expr × Expr) :=
  match ty.app2? ``And with
  | some (a, b) => andLeaves (mkApp3 (mkConst ``And.left) a b pf) a ++ andLeaves (mkApp3 (mkConst ``And.right) a b pf) b
  | none => #[(pf, ty)]

/-- Make the unchanged conjunct or antecedent available as a side condition. -/
def zoomWithHyp (lem : Name) : TacticM Bool := do
  let s ← saveState
  try
    let goal ← getMainGoal
    let gs ← goal.apply (← mkConstWithFreshMVarLevels lem)
    let gs ← gs.filterM fun g => return !(← g.isAssigned)
    let [g] := gs | s.restore; return false
    setGoals [g]
    evalTactic (← `(tactic| intro h))

    let g ← getMainGoal
    let d := (← g.getDecl).lctx.lastDecl.get!
    let ls := andLeaves (mkFVar d.fvarId) d.type
    if ls.size > 1 then
      let hyps := ls.mapIdx fun i (pf, ty) => ({ userName := Name.mkSimple s!"h_{i + 1}", type := ty, value := pf } : Hypothesis)
      let (_, g') ← g.assertHypotheses hyps
      replaceMainGoal [g']
    return true
  catch _ =>
    s.restore
    return false

/-- Descend through a shared connective or binder into the single part that changes. -/
def zoomIn : TacticM Bool := do
  let s ← saveState
  let ty ← instantiateMVars (← getMainTarget)
  let some (a, b) := ty.iff? | return false
  let sameHead (n : Name) (k : Nat) := a.isAppOfArity n k && b.isAppOfArity n k
  let hypLems : List Name :=
    if sameHead ``And 2 then [``and_congr_right, ``and_congr_left]
    else if sameHead ``PT.Imp 2 then [``PT.Imp.congr_right]
    else []
  for lem in hypLems do
    if ← zoomWithHyp lem then return true
  let lem? : Option Name :=
    if sameHead ``And 2 then some ``and_congr
    else if sameHead ``Or 2 then some ``or_congr
    else if sameHead ``Not 1 then some ``not_congr
    else if sameHead ``Iff 2 then some ``iff_congr
    else if sameHead ``PT.Imp 2 then some ``PT.Imp.congr
    else if sameHead ``PT.Forall 3 then some ``PT.Forall.congr
    else if sameHead ``PT.Ex 3 then some ``PT.Ex.congr
    else if sameHead ``PT.wp 4 then some ``PT.wp_congr
    else none
  let some lem := lem? | return false
  try
    let goal ← getMainGoal
    let gs ← goal.apply (← mkConstWithFreshMVarLevels lem)
    let mut remaining := []
    for g in gs do
      if ← g.isAssigned then continue
      setGoals [g]
      if ← focusMain do evalTactic (← `(tactic| intros; with_reducible rfl)) then continue
      remaining := remaining ++ [g]
    if remaining.isEmpty then s.restore; return false
    setGoals remaining
    if lem == ``PT.Forall.congr || lem == ``PT.Ex.congr then
      let body := a.getArg! 2
      let x := if body.isLambda then body.bindingName! else `x
      let hx := Name.mkSimple s!"h_{x}"
      evalTactic (← `(tactic| intro $(mkIdent x):ident))
      evalTactic (← `(tactic| try intro $(mkIdent hx):ident))
    else if lem == ``PT.wp_congr then
      let post := a.getArg! 2
      let x := if post.isLambda then post.bindingName! else `σ
      evalTactic (← `(tactic| intro $(mkIdent x):ident))
    return true
  catch _ =>
    s.restore
    return false

/-! ## Arithmetic -/

def isAssumeHyp (d : LocalDecl) : Bool :=
  let cs := d.userName.toString.toList
  !d.userName.hasMacroScopes && cs.length > 1 && cs.head! == 'h' && (cs.drop 1).all fun c => c.isDigit || c == '_'

/-- At most this many different relations in an arithmetic fact, counting the assumptions cited. -/
def arithLimit : Nat := 4

partial def relations (e : Expr) : Array Expr :=
  let merge (xs ys : Array Expr) := ys.foldl (fun acc y => if acc.contains y then acc else acc.push y) xs
  if e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 || e.isAppOfArity ``Iff 2
      || e.isAppOfArity ``PT.Imp 2 then
    merge (relations (e.getArg! 0)) (relations (e.getArg! 1))
  else if e.isAppOfArity ``Not 1 then relations (e.getArg! 0)
  else if e.isConstOf ``PT.T || e.isConstOf ``PT.F || e.isConstOf ``True || e.isConstOf ``False then #[]
  else match e with
    | .mdata _ b => relations b
    | .forallE _ _ b _ => relations b
    | _ => #[e]

def proveArith (f : Expr) (hide : Array FVarId := #[]) : TacticM (Option Expr) := do
  unless hasArith f do return none
  let g ← mkFreshExprMVar f
  let gs ← getGoals
  let s ← saveState
  try
    let mut m := g.mvarId!
    for h in hide do m ← m.tryClear h
    setGoals [m]
    evalTactic (← `(tactic| intros))
    arithScript
    if (← getUnsolvedGoals).isEmpty then
      setGoals gs
      return some (← instantiateMVars g)
  catch _ => pure ()
  s.restore
  return none

def normTF (e : Expr) : Expr :=
  let e := e.consumeMData
  let isT (c : Expr) := c.isConstOf ``PT.T || c.isConstOf ``True
  let isF (c : Expr) := c.isConstOf ``PT.F || c.isConstOf ``False
  match e.iff? with
  | some (a, b) =>
    if isT b then a.consumeMData else if isT a then b.consumeMData
    else if isF b then mkNot a.consumeMData else if isF a then mkNot b.consumeMData
    else e
  | none => e

def isLiteral (e : Expr) : Bool :=
  let e := normTF e
  let e := if e.isAppOfArity ``Not 1 then normTF (e.getArg! 0) else e
  !(e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 || e.isAppOfArity ``Iff 2
    || e.isAppOfArity ``PT.Imp 2 || e.isAppOfArity ``Not 1)

partial def leaves (op : Name) (e : Expr) : Array Expr :=
  match e.consumeMData.app2? op with
  | some (a, b) => leaves op a ++ leaves op b
  | none => #[e]

def decidedUnder (ctx : Array Expr) (e : Expr) (hide : Array FVarId := #[]) :
    TacticM (Option Bool) := do
  let under (p : Expr) : TacticM Bool := do
    let f ← ctx.foldrM (fun h acc => mkArrow h acc) p
    return (← proveArith f hide).isSome
  if ← under e then return some true
  if ← under (mkNot e) then return some false
  return none

structure Smaller where

  part : Expr

  ctx : Array Expr := #[]

  holds : Bool

  byAssumptions : Bool := false

  isRel : Bool

/-- Find a proper part decided independently, by cited assumptions, or by its context.
Exclude the conclusion and its conjuncts, which may follow from the antecedents. -/
partial def smallerFact (e : Expr) (hide : Array FVarId) (useAssumptions : Bool)
    (ctx : Array Expr := #[]) (whole : Bool := true) (conclusion : Bool := false)
    (listOk : Bool := true) : TacticM (Option Smaller) := do
  let e := normTF e
  let decide (ctx : Array Expr) (p : Expr) : TacticM (Option (Bool × Bool)) := do
    if let some h ← decidedUnder ctx p hide then return some (h, false)
    if useAssumptions then
      if let some h ← decidedUnder ctx p then return some (h, true)
    return none
  let isAnd := e.isAppOfArity ``And 2
  if isLiteral e then
    if whole then return none
    if let some (holds, byAssumptions) ← decide #[] e then
      return some { part := e, holds, byAssumptions, isRel := true }
    if !conclusion && !ctx.isEmpty then
      if let some (holds, byAssumptions) ← decide ctx e then
        return some { part := e, ctx, holds, byAssumptions, isRel := true }
    return none
  if whole && listOk && isAnd && (leaves ``And e).all isLiteral then return none
  unless whole do
    if let some (holds, byAssumptions) ← decide #[] e then
      return some { part := e, holds, byAssumptions, isRel := false }
  let go (e : Expr) (ctx : Array Expr) (whole conclusion : Bool) :=
    smallerFact e hide useAssumptions ctx whole conclusion false
  if isAnd || e.isAppOfArity ``Or 2 then
    let op := if isAnd then ``And else ``Or
    (leaves op e).findSomeM? fun l => go l ctx false (conclusion && isAnd)
  else if let some (a, b) := e.iff? then
    match ← go a ctx false false with
    | some r => pure (some r)
    | none => go b ctx false false
  else if let some (a, b) := e.app2? ``PT.Imp then
    match ← go a ctx false false with
    | some r => pure (some r)
    | none => go b (ctx.push a) false (whole || conclusion)
  else if e.isAppOfArity ``Not 1 then
    go (e.getArg! 0) ctx whole conclusion
  else pure none

/-- Reject a compound fact when a smaller cluster already decides it. -/
def redundantPart (e : Expr) (hide : Array FVarId) (useAssumptions : Bool) : TacticM (Option MessageData) := do
  let e := normTF e
  let decide (p : Expr) : TacticM (Option Bool) := do
    if let some h ← decidedUnder #[] p hide then return some h
    if useAssumptions then decidedUnder #[] p else return none
  let pp (x : Expr) : TacticM String := do return toString (← Meta.ppExpr x)
  let rebuild (op : Name) (ls : Array Expr) : Expr :=
    ls[1:].foldl (fun acc l => mkApp2 (mkConst op) acc l) ls[0]!
  let neg := e.isAppOfArity ``Not 1
  let core := if neg then e.getArg! 0 else e
  if core.isAppOfArity ``Or 2 && !neg then
    let ls := leaves ``Or core
    if ls.size ≥ 3 then
      for l in ls do
        let rest := rebuild ``Or (ls.filter (· != l))
        if (← decide rest) == some true then
          return some m!"`{← pp rest}` holds without `{← pp l}`. Take it as the fact, and join `{← pp l}` by the laws"
  else if core.isAppOfArity ``And 2 && neg then
    let ls := leaves ``And core
    if ls.size ≥ 3 then
      for l in ls do
        let rest := rebuild ``And (ls.filter (· != l))
        if (← decide rest) == some false then
          return some m!"`({← pp rest}) = F` holds without `{← pp l}`. Take it as the fact, and join `{← pp l}` by the laws"
  return none

def smallerMessage (text : String) (sm : Smaller) (cited : List String) : TacticM MessageData := do
  let pp (e : Expr) : TacticM String := do return toString (← Meta.ppExpr e)
  let part ← pp sm.part
  let tf := if sm.holds then "T" else "F"
  let head := m!"the arithmetic fact `{text}` contains a smaller fact, "
  let rest := "and the rest by the laws"
  let asFact := if sm.holds then part else s!"({part}) = F"
  unless sm.ctx.isEmpty do
    let ctx := " ∧ ".intercalate (← sm.ctx.toList.mapM pp)
    return head ++ m!"`{part}` is {tf} under `{ctx}`. Take the relation as the fact, \{Arithmetic: {ctx} ⇒ (({part}) = {tf})}, {rest}"
  let what := if sm.isRel then m!"`{part}` is {tf}" else m!"`{part}` {if sm.holds then "holds" else "fails"}"
  if sm.byAssumptions then
    let hint := ", ".intercalate (["Conditional Substitution"] ++ cited ++ [s!"Arithmetic: {asFact}"])
    return head ++ what ++ m!" by the assumptions cited. Take it as a step, \{{hint}}, {rest}"
  return head ++ what ++ m!" by itself. Take it as a step, \{Arithmetic: {asFact}}, {rest}"

/-- Accept relations, their combinations, and conditional relations. -/
def arithShape (e : Expr) : Bool :=
  let cluster (op : Name) (e : Expr) := (leaves op e).all isLiteral
  let side (e : Expr) :=
    let e := normTF e
    isLiteral e || cluster ``And e || cluster ``Or e
      || (e.isAppOfArity ``Not 1 && (cluster ``And (e.getArg! 0) || cluster ``Or (e.getArg! 0)))

  let eqn (a b : Expr) := side a && side b && (isLiteral (normTF a) || isLiteral (normTF b))
  let e := normTF e
  if side e then true
  else if let some (a, b) := e.iff? then eqn a b
  else if let some (a, b) := e.app2? ``PT.Imp then
    let a := normTF a
    let b := normTF b
    (isLiteral a || cluster ``And a)
      && (isLiteral b || cluster ``And b || (match b.iff? with | some (x, y) => eqn x y | none => false))
  else false

partial def evalProp (atoms : Array Expr) (val : Array Bool) (e : Expr) : Bool :=
  let e := e.consumeMData
  if let some (a, b) := e.app2? ``And then evalProp atoms val a && evalProp atoms val b
  else if let some (a, b) := e.app2? ``Or then evalProp atoms val a || evalProp atoms val b
  else if let some (a, b) := e.app2? ``PT.Imp then !evalProp atoms val a || evalProp atoms val b
  else if let some (a, b) := e.iff? then evalProp atoms val a == evalProp atoms val b
  else if e.isAppOfArity ``Not 1 then !evalProp atoms val (e.getArg! 0)
  else if e.isConstOf ``PT.T || e.isConstOf ``True then true
  else if e.isConstOf ``PT.F || e.isConstOf ``False then false
  else match atoms.findIdx? (· == e) with
    | some i => val[i]!
    | none => false

/-- Merge equal or opposite relations, using contextual equations only.
Keep antecedent atoms distinct to avoid treating consequences as assumptions. -/
def mergedAtoms (atoms : Array Expr) (hide : Array FVarId) (fixed : Array Expr) (ctx : Array Expr) : TacticM (Array (Nat × Bool)) := do
  let same (a b : Expr) : TacticM Bool := do
    let plain := (← decidedUnder #[] (mkApp2 (mkConst ``Iff) a b) hide) == some true
    if fixed.contains a || fixed.contains b then
      if plain || ctx.isEmpty then return false
      return (← decidedUnder ctx (mkApp2 (mkConst ``Iff) a b) hide) == some true
    if plain then return true
    return (← decidedUnder ctx (mkApp2 (mkConst ``Iff) a b) hide) == some true
  let mut cls : Array (Nat × Bool) := #[]
  for i in [0:atoms.size] do
    let mut found : Option (Nat × Bool) := none
    for j in [0:i] do
      if found.isSome then break
      if fixed.contains atoms[i]! && fixed.contains atoms[j]! then continue
      let (cj, sj) := cls[j]!
      if ← same atoms[i]! atoms[j]! then found := some (cj, sj)
      else if ← same atoms[i]! (mkNot atoms[j]!) then found := some (cj, !sj)
    cls := cls.push (found.getD (i, true))
  return cls

/-- Recognize propositional tautologies after merging equivalent arithmetic atoms. -/
def propTautology (e : Expr) (hide : Array FVarId := #[]) (ctx : Array Expr := #[]) : TacticM (Option (Array (Nat × Bool))) := do
  let atoms := relations e
  if atoms.isEmpty || atoms.size > 6 then return none
  let n := atoms.size
  let taut (cls : Array (Nat × Bool)) : Bool :=
    (List.range (2 ^ n)).all fun k =>
      let base := (Array.range n).map fun i => (k / 2 ^ i) % 2 == 1
      evalProp atoms (cls.map fun (c, s) => base[c]! == s) e
  let plain := (Array.range n).map fun i => (i, true)
  if taut plain then return some plain
  if n < 3 then return none

  let cls ← mergedAtoms atoms hide (ctx.flatMap relations) (ctx.filter (·.isAppOfArity ``Eq 3))
  if cls == plain then return none
  return if taut cls then some cls else none

/-- Reject arithmetic facts that conceal smaller steps or propositional reasoning. -/
def notOneLaw (text : String) (f : Expr) (cited : List (String × Expr)) (assumed : Array FVarId)
    (needed : Bool) : TacticM (Option MessageData) := do
  forallTelescope f fun _ body => do
    if let some sm ← smallerFact body assumed needed then
      return some (← smallerMessage text sm (cited.map (·.1)))
    if let some msg ← redundantPart body assumed needed then
      return some (m!"the arithmetic fact `{text}` is two facts, " ++ msg)
    if !arithShape body then
      return some m!"the arithmetic fact `{text}` is not one law of arithmetic: a relation, an equation between relations or their conjunctions and disjunctions, or an implication from relations to a relation, as in appendix 4. Its other connectives are for the laws"

    let citedF := cited.map (·.2)
    let conj (fs : List Expr) : Expr := match fs with
      | [] => mkConst ``True
      | c :: cs => cs.foldl (fun acc d => mkApp2 (mkConst ``And) acc d) c
    let b := normTF body
    let parts := if b.isAppOfArity ``And 2 && (leaves ``And b).all isLiteral then leaves ``And b else #[body]
    for part in parts do

      if citedF.any (· == part) then continue

      let mut relevant : List Expr := citedF
      for c in citedF do
        let others := relevant.filter (· != c)
        let without := if others.isEmpty then part else mkApp2 (mkConst ``PT.Imp) (conj others) part
        if (← proveArith without assumed).isSome then relevant := others
      let whole := match relevant with
        | [] => part
        | _ =>
          let ante := conj relevant
          match (normTF part).app2? ``PT.Imp with
          | some (a, b) => mkApp2 (mkConst ``PT.Imp) (mkApp2 (mkConst ``And) ante a) b
          | none => mkApp2 (mkConst ``PT.Imp) ante part
      if !relevant.isEmpty && !arithShape whole then
        return some m!"the arithmetic fact `{text}` with the assumptions cited is not one law of arithmetic: an assumption that is a disjunction is a case analysis, take the cases by Proof by Cases, and a connective in it is for the laws"

      let ante := match (normTF part).app2? ``PT.Imp with
        | some (a, _) => leaves ``And a
        | none => #[]
      if let some cls ← propTautology whole assumed (relevant.toArray ++ ante) then
        let names := #["p", "q", "r", "s", "t", "u"]
        let mut withs : List String := []
        for a in relations whole, (c, s) in cls do
          withs := withs ++ [s!"`{if s then "" else "¬"}{names[c]!}` for `{← Meta.ppExpr a}`"]
        let withAss := if relevant.isEmpty then m!"" else m!" with the assumptions cited"
        return some m!"the arithmetic fact `{text}`{withAss} holds by the propositional laws alone, with {", ".intercalate withs}. Calculate it by the laws"
    return none

partial def identsOf (stx : Syntax) : Array Name :=
  match stx with
  | .ident _ _ n _ => #[n]
  | .node _ _ args => args.foldl (fun acc a => acc ++ identsOf a) #[]
  | _ => #[]

/-- Free names in an arithmetic hint become universally quantified integer dummies. -/
def elabFact (text : String) : TacticM (Option Expr) := do
  match Parser.runParserCategory (← getEnv) `ptf text.trimAscii.toString with
  | .error _ => return none
  | .ok stx =>
    let stx := noPositions stx
    let lctx ← getLCtx
    let env ← getEnv
    let stName? ← stateName?
    let mut dummies : Array Name := #[]
    for id in identsOf stx do
      if [`T, `F, `true, `false, `True, `False].contains id then continue
      if (lctx.findFromUserName? id).isSome then continue
      if env.contains id || env.contains (`PT ++ id) then continue
      if let some st := stName? then
        if env.contains (st ++ id) then continue
      unless dummies.contains id do dummies := dummies.push id
    let decls : Array (Name × (Array Expr → TacticM Expr)) := dummies.map fun n => (n, fun _ => pure (mkConst ``Int))
    withLocalDeclsD decls fun xs => do
      try

        let stx ← reassoc stx
        let t ← `(⟪$(⟨stx⟩):ptf⟫)
        let e ← Term.withoutErrToSorry <| Tactic.elabTerm t (some (mkSort .zero))
        Term.synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        return some (← mkForallFVars xs e)
      catch _ => return none

/-! ## The step -/

structure Move where

  item : String

  laws : Array Name := #[]

  hyps : Array LocalDecl := #[]

  part : Option Expr := none
  /-- Translate again inside binders and `wp` to use their local dummy and state. -/
  partText : Option String := none
  deriving Inhabited

def lawStatement (c : Name) : MetaM String := do
  let some ci := (← getEnv).find? c | return toString c
  forallTelescope ci.type fun _ body => do
    let body := match body.app2? ``PT.Imp with
      | some (_, b) => if b.isAppOfArity ``Iff 2 || b.isAppOfArity ``Eq 3 then b else body
      | none => body
    return toString (← ppExpr body)

/-- Use only cited assumptions, including their conjuncts. -/
def scopeAssumptions (cited : Array (LocalDecl × Expr)) : TacticM Unit := withMainContext do
  let mut goal ← getMainGoal
  let mut hyps : Array Hypothesis := #[]
  let mut clear : Array FVarId := #[]
  for d in ← getLCtx do
    unless isAssumeHyp d do continue
    let fs := cited.filterMap fun (o, f) => if o.fvarId == d.fvarId then some f else none
    if fs.isEmpty then clear := clear.push d.fvarId; continue
    unless d.type.isAppOfArity ``And 2 do continue

    let whole ← fs.anyM fun f => withReducible (isDefEq f d.type)
    for (pf, ty) in andLeaves (mkFVar d.fvarId) d.type, i in [0:100] do
      if whole || (← fs.anyM fun f => withReducible (isDefEq f ty)) then
        hyps := hyps.push { userName := Name.mkSimple s!"{d.userName}_{i + 1}", type := ty, value := pf }
    unless whole do clear := clear.push d.fvarId
  goal := (← goal.assertHypotheses hyps).2
  for f in clear do goal ← goal.tryClear f
  replaceMainGoal [goal]

structure Src where
  name : String
  make : MetaM (Array (Expr × Expr))
  schema : Bool := false

def Src.descr (src : Src) : Option Expr → MessageData
  | some u => m!"{src.name} applied to `{u}`"
  | none => m!"{src.name}"

/-- Also offer a conditional law as a formula equivalent to `T`. -/
def formulaOfConditional (c : Name) : MetaM (Option (Expr × Expr)) := do
  let e ← mkConstWithFreshMVarLevels c
  let mut e := e
  let mut ty ← instantiateMVars (← inferType e)
  while ty.isForall do
    if ← isProp ty.bindingDomain! then
      let f := mkApp2 (mkConst ``PT.Imp) ty.bindingDomain! ty.bindingBody!
      return some (mkApp2 (mkConst ``PT.iffT) f e, mkApp2 (mkConst ``Iff) f (mkConst ``PT.T))
    let m ← mkFreshExprMVar ty.bindingDomain!
    e := mkApp e m
    ty := ty.bindingBody!.instantiate1 m
  if let some (cnd, body) := ty.app2? ``PT.Imp then
    if body.isAppOfArity ``Iff 2 || body.isAppOfArity ``Eq 3 then
      let f := mkApp2 (mkConst ``PT.Imp) cnd body
      return some (mkApp2 (mkConst ``PT.iffT) f e, mkApp2 (mkConst ``Iff) f (mkConst ``PT.T))
  return none

def isCondRewrite (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | none => false
  | some ci =>
    match (stripForall ci.type).app2? ``PT.Imp with
    | some (_, b) => b.isAppOfArity ``Iff 2 || b.isAppOfArity ``Eq 3
    | none => false

def sourcesOf (mv : Move) (isImp : Bool) : TacticM (Array Src) := do
  let env ← getEnv
  let mut out : Array Src := #[]
  for c in mv.laws do
    let kind := if classify env c == .imp && isCondRewrite env c then .equiv else classify env c
    match kind with
    | .equiv =>
      out := out.push { name := s!"`{mv.item}`", make := do
        let (e, ty) ← instantiateLaw c
        (← acVariants e ty).mapM fun v => do pure (v, ← instantiateMVars (← inferType v)) }
      if ← hasCondition c then
        out := out.push { name := s!"`{mv.item}`", make := do
          match ← formulaOfConditional c with
          | some p => pure #[p]
          | none => pure #[] }
    | .schema =>
      out := out.push { name := s!"`{mv.item}`", make := do pure #[← instantiateLaw c], schema := true }
    | .imp =>
      -- an implication in an `=` step is the formula `(X ⇒ Y) = T`
      unless isImp do
        out := out.push { name := s!"`{mv.item}`", make := do
          let e ← mkConstWithFreshMVarLevels c
          let (args, ty) ← lawTelescope e
          (← impVariants (← lawApp e args ty) ty).mapM fun v => do
            let t ← instantiateMVars (← inferType v)
            pure (mkApp2 (mkConst ``PT.iffT) t v, mkApp2 (mkConst ``Iff) t (mkConst ``PT.T)) }
    | .other =>

      out := out.push { name := s!"`{mv.item}`", make := do
        let (e, ty) ← instantiateLaw c
        pure #[(mkApp2 (mkConst ``PT.iffT) ty e, mkApp2 (mkConst ``Iff) ty (mkConst ``PT.T))] }
  for d in mv.hyps do
    out := out.push { name := s!"`{mv.item}`", make := do
      let (args, ty) ← lawTelescope (mkFVar d.fvarId)
      let e := mkAppN (mkFVar d.fvarId) args

      let f := mkApp2 (mkConst ``PT.iffT) ty e
      let t := mkApp2 (mkConst ``Iff) ty (mkConst ``PT.T)
      let mut vs ← (← acVariants f t).mapM fun v => do pure (v, ← instantiateMVars (← inferType v))

      if ty.isAppOfArity ``Iff 2 || ty.isAppOfArity ``Eq 3 then
        vs := vs ++ (← (← acVariants e ty).mapM fun v => do pure (v, ← instantiateMVars (← inferType v)))

      if let some (cnd, body) := ty.app2? ``PT.Imp then
        if body.isAppOfArity ``Iff 2 || body.isAppOfArity ``Eq 3 then
          let e := mkApp e (← mkFreshExprMVar cnd)
          vs := vs ++ (← (← acVariants e body).mapM fun v => do pure (v, ← instantiateMVars (← inferType v)))
      pure vs }
  return out

/-- Try one variant and direction. `inNext` requires its result in the next line. -/
def attempt (src : Src) (i : Nat) (symm : Bool) (u? : Option Expr) (a : Expr)
    (subsB : Array Expr) (occs : Occurrences) (inNext : Bool) (sc : Scope)
    (close : Option (TacticM Bool)) : TacticM (Option FailKind) := do
  let s ← saveState
  let fail (f : FailKind) : TacticM (Option FailKind) := do s.restore; return some f
  try
    let vs ← src.make
    let some (v, vty) := vs[i]? | return ← fail .noMatch
    let some (l, r) := (vty.iff? <|> (vty.eq?.map fun (_, x, y) => (x, y))) | return ← fail .noMatch
    let (pat, res) := if symm then (r, l) else (l, r)
    let pat ← instantiateMVars pat
    if src.schema then
      let some t := u? | return ← fail .noMatch
      unless ← schemaInstance v pat a t do return ← fail .noMatch
    else
      match u? with
      | some u =>
        unless ← isDefEq pat u do return ← fail .noMatch
      | none =>

        unless isBare pat do return ← fail .noMatch
        let mut found := false
        for w in subsB do
          let s' ← saveState
          if ← isDefEq res w then found := true; break
          s'.restore
        unless found do return ← fail .noMatch
    unless ← fixFromNext v res subsB do return ← fail .open_
    if inNext then
      unless subsB.contains (← instantiateMVars res) do return ← fail .noMatch
    match ← rewriteLeft v symm occs sc with
    | some (.condition c assumed _) =>

      match close with
      | some cl =>
        let a' := (stepSides (← instantiateMVars (← getMainTarget))).map (·.1) |>.getD a
        let s' ← saveState
        let r ← try cl catch _ => pure false
        s'.restore
        if r then fail (.condition c assumed true)
        else if assumed then fail (.condition c true false)
        else fail (.mismatch (src.descr u?) a' symm true)
      | none => fail (.condition c assumed false)
    | some f => fail f
    | none => return none
  catch _ => fail .noMatch

/-- Prefer a result that occurs in the next line. The last move must close the goal.
Reject returns to an earlier intermediate line. -/
def applyHere (mv : Move) (srcs : Array Src) (close : Option (TacticM Bool)) (sc : Scope)
    (seen : Array Expr) : TacticM (Option Fail) := do
  let env ← getEnv
  let goalTy ← instantiateMVars (← getMainTarget)
  let some (a, b) := stepSides goalTy | return none
  let isImp := goalTy.isAppOfArity ``PT.Imp 2
  let subsA ← subterms a
  let subsB ← subterms b
  let mkFail (k : FailKind) : Fail := { line := a, next := b, kind := k }
  -- Re-read the selected part in this binder or `wp` state.

  let partNow : Option Expr ← match mv.partText with
    | some t => do
      match ← elabHintFormula t with
      | some u => pure (some u)
      | none => return some (mkFail .noMatch)
    | none => pure mv.part
  let mut worst : Option Fail := none

  if isImp then
    for c in mv.laws do
      if classify env c != .imp || isCondRewrite env c then continue
      let make : MetaM (Array Expr) := do
        let e ← mkConstWithFreshMVarLevels c
        let (args, ty) ← lawTelescope e
        impVariants (← lawApp e args ty) ty
      let s ← saveState
      try
        monoApply make 6 (← IO.mkRef false)
        let mut ok := true
        for g in ← getGoals do
          if ← g.isAssigned then continue
          unless ← closeCondition g sc.helpers do
            let c ← instantiateMVars (← g.getType)
            worst := some ((mkFail (.condition c (← sc.closable c) false)).better worst)
            ok := false
            break
          let pf ← instantiateMVars (mkMVar g)
          if pf.hasAnyFVar (sc.cited.contains ·) || pf.getUsedConstants.any sc.helpers.contains
              || (← usesLineHyp pf) then
            sc.usedHyp.set true
        if ok then
          setGoals []
          return none
      catch _ => pure ()
      s.restore
      worst := some ((mkFail .noPosition).better worst)
  for src in srcs do

    let (nv, info) ← do
      let s ← saveState
      let vs ← src.make
      let info ← vs.mapM fun (_, ty) => do
        let sides := ty.iff? <|> (ty.eq?.map fun (_, x, y) => (x, y))
        pure ((sides.map fun (l, _) => isBare l).getD false, (sides.map fun (_, r) => isBare r).getD false)
      s.restore
      pure (vs.size, info)
    for symm in [false, true] do
      for i in [0:nv] do
        let bare := if symm then info[i]!.2 else info[i]!.1
        let parts : Array (Option Expr) := match partNow with
          | some u => #[some u]
          | none => if src.schema then subsA.map some else if bare then #[none] else subsA.map some
        let passes : List Bool := match close with
          | some _ => [false]
          | none => [true, false]
        for inNext in passes do
          for u? in parts do
            -- A referenced theorem can rewrite at most one occurrence.
            -- Assumptions and arithmetic facts may replace all occurrences.

            let occsList : List Occurrences :=
              if mv.laws.isEmpty then (if bare then [.pos [1]] else [.all])
              else match close with
                | some _ => [.pos [1], .pos [2], .pos [3], .pos [4]]
                | none => [.pos [1]]
            for occs in occsList do
              let before ← saveState
              match ← attempt src i symm u? a subsB occs inNext sc close with
              | some f =>
                worst := some ((mkFail f).better worst)
                break
              | none =>
                let a' := (stepSides (← instantiateMVars (← getMainTarget))).map (·.1) |>.getD a
                if seen.contains a' then
                  before.restore
                  continue
                match close with
                | none => return none
                | some cl =>
                  if ← cl then return none
                  worst := some ((mkFail (.mismatch (src.descr u?) a' symm false)).better worst)
                  before.restore
  return some (worst.getD (mkFail .noMatch))

def flipGoal : TacticM Bool := do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  if let some (a, b) := ty.iff? then
    let g' ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``Iff) b a)
    goal.assign (mkApp3 (mkConst ``Iff.symm) b a g')
    replaceMainGoal [g'.mvarId!]
    return true
  if let some (_, a, b) := ty.eq? then
    let g' ← mkFreshExprSyntheticOpaqueMVar (← mkEq b a)
    goal.assign (← mkEqSymm g')
    replaceMainGoal [g'.mvarId!]
    return true
  return false

/-- Apply here or descend into the changing part. -/
partial def applyMove (mv : Move) (srcs : Array Src) (close : Option (TacticM Bool)) (sc : Scope)
    (seen : Array Expr) (depth : Nat) : TacticM (Option Fail) := do
  match ← withMainContext (applyHere mv srcs close sc seen) with
  | none => return none
  | some f =>
    if depth == 0 then return some f
    let s ← saveState
    if ← zoomIn then

      let gs ← getGoals
      let mut inner : Option Fail := none
      for g in gs do
        let s' ← saveState
        setGoals ([g] ++ gs.filter (· != g))
        match ← applyMove mv srcs close sc seen (depth - 1) with
        | none => return none
        | some f' =>
          s'.restore
          inner := some (match inner with | none => f' | some i => i.better (some f'))
      s.restore
      if let some f' := inner then
        -- Prefer a local failure unless a broad reverse match makes it uninformative.

        match f'.kind with
        | .noMatch | .mismatch _ _ true _ => return some f
        | _ => return some (f.better (some f'))
    return some f

def failMessage (mv : Move) (f : Fail) (probe : Option LocalDecl → Expr → TacticM Bool) (uncited : Array LocalDecl)
    (citedItems : List String) (isImp : Bool) : TacticM MessageData := do
  let X := mv.item
  let a := f.line
  let env ← getEnv
  let implication := !mv.laws.isEmpty && mv.laws.all fun c => classify env c == .imp && !isCondRewrite env c
  if implication && !isImp then
    match f.kind with
    | .noMatch | .open_ =>
      return m!"`{X}` is an implication, it justifies a `⇒` step, or as a formula the step `(A ⇒ B) = T`"
    | _ => pure ()
  match f.kind with
  | .mismatch descr a' _ _ =>
    let other := if f.flipped then "line above" else "next line"
    return m!"{descr} gives{indentExpr a'}\nbut the {other} is{indentExpr f.next}"
  | .noMatch =>
    if let some u := mv.part then
      return m!"`{X}` does not apply to `{u}` in{indentExpr a}"
    if let some t := mv.partText then
      return m!"`{X}` does not apply to `{t}` in{indentExpr a}"
    let stmts ← mv.laws.toList.take 3 |>.mapM fun c => do return (← lawStatement c)
    let stmts := if mv.laws.size > 3 then stmts ++ ["…"] else stmts
    if stmts.isEmpty then return m!"`{X}` does not apply to any part of{indentExpr a}"
    let listed := "\n".intercalate (stmts.map fun s => "  " ++ s)
    return m!"`{X}` does not apply to any part of{indentExpr a}\n{X} is\n{listed}"
  | .open_ =>
    return m!"the instance of `{X}` is not determined by the line and the next line, name the part, `{X}: …`"
  | .noPosition =>
    return m!"`{X}` does not apply at the top of the line or under ∧, ∨, ¬ and ⇒{indentExpr a}"
  | .condition c _ _ =>

    let listed := (pt.assumed.get (← getOptions)).splitOn "\u0001" |>.filter (· ≠ "")
    let nameOf (d : LocalDecl) : TacticM String := do
      let idx := (d.userName.toString.drop 1).toString.toNat?.getD 0
      return listed[idx - 1]?.getD (toString (← Meta.ppExpr d.type))
    let mut names : Array String := #[]
    let mut needFact := false
    for (_, part) in andLeaves (mkConst ``True) c do
      if ← uncited.anyM fun d => withReducible (isDefEq d.type part) then
        for d in uncited do
          if ← withReducible (isDefEq d.type part) then
            let n ← nameOf d
            unless names.contains n do names := names.push n
            break
        continue
      if ← probe none part then

        let g ← mkFreshExprMVar part
        unless ← closedArith g.mvarId! do needFact := true
        continue
      let mut found := false
      for d in uncited do
        if ← probe (some d) part then
          let n ← nameOf d
          unless names.contains n do names := names.push n
          needFact := true
          found := true
          break
      unless found do
        return m!"`{X}` needs{indentExpr c}\nwhich does not follow by arithmetic from the assumptions of the proof"
    let ctext ← Meta.ppExpr c
    let extra := names.toList.map (s!"Assumption: {·}") ++ (if needFact then [s!"Arithmetic: {ctext}"] else [])
    let extra := extra.filter (!citedItems.contains ·)
    let hint := ", ".intercalate (["Conditional Substitution"] ++ citedItems ++ extra ++ [X])
    let ask := if needFact then "cite what it follows from" else "cite the assumption"
    return m!"`{X}` needs{indentExpr c}\n{ask}, \{{hint}}"

partial def checkStep (hintText : String) (hintStx : Syntax := .missing) : TacticM Unit := do
  let env ← getEnv
  let opts ← getOptions
  let maxSec := pt.sections.get opts
  let goal ← getMainGoal
  let goalTy ← instantiateMVars (← goal.getType)
  let some (a, _) := stepSides goalTy | throwError "not a step"
  let isImp := goalTy.isAppOfArity ``PT.Imp 2
  let items := parseHint hintText
  if items.isEmpty then throwError "empty hint"
  let listed := (pt.assumed.get opts).splitOn "\u0001" |>.filter (· ≠ "")
  let hint := s!"\{{hintText}}"
  -- Item kinds are 0 for a theorem, 1 for an assumption, and 2 for an arithmetic fact.
  let mut moves : Array Move := #[]
  let mut assumptions : Array Move := #[]
  let mut facts : Array (String × Expr) := #[]
  let mut condSubst := false
  let mut acOnly := true
  let mut anyCondition := false
  let mut order : Array (Nat × Nat) := #[]

  let mut helperItems : Array Nat := #[]
  for (name, part) in items do
    let k := normalizeHint name
    if k == "conditionalsubstitution" then condSubst := true; continue
    if k == "arithmetic" || k == "arith" then
      acOnly := false
      let some text := part | throwError "`{name}` names the arithmetic fact it uses, as `Arithmetic: m ≤ m + 1`"
      let some f ← elabFact text | throwError "`{text}` is not a formula"
      order := order.push (2, facts.size)
      facts := facts.push (text, f)
      continue
    if isAssumptionKey k then
      acOnly := false
      let some text := part | throwError "`{name}` names the assumption it uses, as `Assumption: p`"
      let some f ← elabHintFormula text | throwError "`{text}` is not a formula of this proof"

      let mut hyps : Array LocalDecl := #[]
      for d in ← getLCtx do
        if isAssumeHyp d then
          if ← (#[(mkFVar d.fvarId, d.type)] ++ andLeaves (mkFVar d.fvarId) d.type).anyM fun (_, ty) => withReducible (isDefEq ty f) then
            hyps := hyps.push d
      if hyps.isEmpty then
        let line := if listed.isEmpty then m!"" else m!", the `assume` line has {", ".intercalate listed}"
        throwError "`{text}` is not an assumption of this proof{line}"
      order := order.push (1, assumptions.size)
      assumptions := assumptions.push { item := "Assumption: " ++ text, hyps := hyps, part := some f }
      continue
    let names := lookupHint env name maxSec (← getCurrNamespace)
    if names.isEmpty then throwError (unknownHint env name maxSec)
    addHintInfo hintStx hintText name names[0]!
    for n in names do
      unless (`PT).isPrefixOf n do
        if (← collectAxioms n).contains ``sorryAx then throwError "`{name}` is not proved (its proof uses `sorry`)"
        if pt.strict.get (← getOptions) && relaxedTag.hasTag env n then
          throwError "`{name}` was checked with weakened options; recheck it without relaxed options before citing it"
    let partE ← match part with
      | some t => do
        match ← elabHintFormula t with
        | some u => pure (some u)
        | none =>

          unless (← elabFact t).isSome do throwError "`{t}` is not a formula"
          pure none
      | none => pure none
    let isAC := names.all fun n => (`PT.Commutativity).isPrefixOf n || (`PT.Associativity).isPrefixOf n
      || n == ``PT.Identity || (`PT.DummyRenaming).isPrefixOf n
    unless isAC do acOnly := false
    if ← names.anyM (fun n => do return (← hasCondition n)) then anyCondition := true
    -- A plain-formula lemma can supply a cited theorem's condition.

    if names.all fun n => classify env n == .other && isUserDecl env n then
      order := order.push (0, moves.size)
      moves := moves.push { item := name, laws := names, part := partE, partText := part }
      helperItems := helperItems.push moves.size
      continue
    order := order.push (0, moves.size)
    moves := moves.push { item := name, laws := names, part := partE, partText := part }

  let cited := assumptions.flatMap fun mv => mv.hyps.map fun d => (d, mv.part.getD d.type)
  let uncited := (← getLCtx).foldl (init := #[]) fun acc d =>
    if isAssumeHyp d && !cited.any (·.1.fvarId == d.fvarId) then acc.push d else acc
  let unsolved ← saveState

  let probeWith (extra : Array LocalDecl) (c : Expr) : TacticM Bool := do
    let s ← saveState
    unsolved.restore
    let ok ← try
        scopeAssumptions (cited ++ extra.map fun d => (d, d.type))
        withMainContext do return (← proveArith c).isSome
      catch _ => pure false
    s.restore
    return ok
  let probe (d? : Option LocalDecl) (c : Expr) : TacticM Bool := probeWith (d?.toArray) c
  let nameOf (d : LocalDecl) : TacticM String := do
    let idx := (d.userName.toString.drop 1).toString.toNat?.getD 0
    return listed[idx - 1]?.getD (toString (← Meta.ppExpr d.type))
  scopeAssumptions cited

  let assumed ← withMainContext do
    (← getLCtx).foldlM (init := #[]) fun acc d => do
      if d.isImplementationDetail then return acc
      if ← isProp d.type then return acc.push d.fvarId else return acc
  let mut factHyps : Array Hypothesis := #[]
  let mut derived : Array Bool := #[]
  for (text, f) in facts, i in [0:facts.size] do
    let rels ← withMainContext do
      let mut rels := relations f
      for d in ← getLCtx do
        if isAssumeHyp d then
          for r in relations d.type do
            unless rels.contains r do rels := rels.push r
      pure rels
    if rels.size > arithLimit then
      unsolved.restore
      throwError "the arithmetic fact `{text}` involves {rels.size} different relations, at most {arithLimit} are allowed at a time, counting the assumptions cited. Take a smaller step"
    match ← withMainContext (proveArith f) with
    | some pf =>
      let needed := pf.hasAnyFVar (assumed.contains ·)
      let cited := assumptions.toList.filterMap fun mv => mv.part.map (mv.item, ·)
      if let some msg ← withMainContext (notOneLaw text f cited assumed needed) then
        unsolved.restore
        throwError msg
      factHyps := factHyps.push { userName := Name.mkSimple s!"a{i + 1}", type := f, value := pf }
      derived := derived.push needed
    | none =>

      let mut names : Array String := #[]
      for d in uncited do
        if ← probe (some d) f then names := names.push (← nameOf d); break
      if names.isEmpty then
        if ← probeWith uncited f then names := ← uncited.mapM nameOf
      unsolved.restore
      if names.isEmpty then
        throwError "the arithmetic fact `{text}` is not established from the cited assumptions. The checker uses linear arithmetic and may reject true facts involving products of variables. Take a smaller step, or cite what it follows from"
      let hint' := ", ".intercalate (names.toList.map (s!"Assumption: {·}") ++ [s!"Arithmetic: {text}"])
      throwError "the arithmetic fact `{text}` uses an assumption of the proof, cite it, \{{hint'}}"
  unless factHyps.isEmpty do
    let mut all := factHyps
    for h in factHyps do
      let ls := andLeaves h.value h.type
      if ls.size > 1 then
        for (pf, ty) in ls, i in [0:ls.size] do
          all := all.push { userName := Name.mkSimple s!"{h.userName}_{i + 1}", type := ty, value := pf }
    let (_, g) ← (← getMainGoal).assertHypotheses all
    replaceMainGoal [g]
  withMainContext do
  -- Track which conditions use assumptions.

  let mut inScope : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    unless ← isProp d.type do continue
    let name := d.userName.toString
    let isFact := name.startsWith "a" && ((name.drop 1).toString.splitOn "_").head!.toNat?.isSome
    if isFact then
      let i := (((name.drop 1).toString.splitOn "_").head!.toNat?.getD 1) - 1
      if derived[i]?.getD false then inScope := inScope.push d.fvarId
    else inScope := inScope.push d.fvarId

  let helpersActive := anyCondition && helperItems.size < moves.size
  let helpers := if helpersActive then helperItems.flatMap (fun i => moves[i - 1]!.laws) else #[]
  let sc : Scope := { cited := inScope, helpers := helpers, usedHyp := ← IO.mkRef false, closable := probeWith uncited }
  -- Arithmetic facts prove side conditions when present. Otherwise they rewrite.

  let suppliersRewrite := !anyCondition
  let assumptionsRewrite := suppliersRewrite && facts.isEmpty
  let hypsOf (f : Expr) : TacticM (Array LocalDecl) := do
    (← getLCtx).foldlM (init := #[]) fun acc d => do
      if d.isImplementationDetail then return acc
      if (← isProp d.type) && (← withReducible (isDefEq d.type f)) then return acc.push d else return acc
  let mut plan : Array Move := #[]
  for (kind, i) in order do
    match kind with
    | 1 =>
      if assumptionsRewrite then
        let mv := assumptions[i]!
        let some f := mv.part | continue
        plan := plan.push { mv with hyps := ← hypsOf f, part := none }
    | 2 =>
      if suppliersRewrite then
        let (text, f) := facts[i]!
        plan := plan.push { item := "Arithmetic: " ++ text, hyps := ← hypsOf f }
    | _ =>
      unless helpersActive && helperItems.contains (i + 1) do plan := plan.push moves[i]!
  -- Lean treats formulas differing only in bound variable names as equal.
  let isRenaming (mv : Move) := !mv.laws.isEmpty && mv.laws.all (`PT.DummyRenaming).isPrefixOf
  let renamed := plan.any isRenaming
  plan := plan.filter (!isRenaming ·)
  if plan.isEmpty && !renamed then throwError "the hint {hint} names no theorem, assumption or fact to apply"

  unless acOnly do
    let s ← saveState
    let byAC ← (pure (← closeByRfl) <||> closeByAC)
    s.restore
    let eq ← closeStep
    s.restore
    if byAC || (eq && facts.isEmpty) then
      unsolved.restore
      throwError "the two lines are already equal, up to order, grouping and integer cancellation, so {hint} is not applied. A trivial step is justified by \{Identity}, \{Commutativity} or \{Associativity}"

    if eq && plan.all (·.laws.isEmpty) then
      if ← closeStep then return
  if acOnly then
    if ← closeStep false then return
    if plan.isEmpty then
      unsolved.restore
      throwError "`Dummy Renaming` changes only the name of a dummy, and the two lines differ in more"

  let citedItems := assumptions.toList.map (·.item) ++ facts.toList.map fun (t, _) => "Arithmetic: " ++ t
  let mut seen : Array Expr := #[a]
  for mv in plan, j in [0:plan.size] do
    let last := j + 1 == plan.size
    let srcs ← sourcesOf mv isImp
    let closer := closeStep
    let r ← applyMove mv srcs (if last then some closer else none) sc seen 8

    let r ← match r with
      | some f =>
        if last then
          let s ← saveState
          if ← flipGoal then
            match ← applyMove mv srcs (some closer) sc seen 8 with
            | none => pure none
            | some f' =>
              s.restore

              pure (some (match f'.kind with
                | .condition _ _ false => f
                | _ => if f'.kind.rank > f.kind.rank then { f' with flipped := true } else f))
          else pure (some f)
        else pure (some f)
      | none => pure none
    match r with
    | none =>

      for _ in [0:8] do
        if (← getGoals).length ≤ 1 then break
        unless (← closeByRfl) || (← closeByAC) do break
      unless (← getGoals).isEmpty do
        if let some (a', _) := stepSides (← instantiateMVars (← getMainTarget)) then seen := seen.push a'
    | some f =>

      if plan.size == 1 && !mv.laws.isEmpty && items.length == 1 then
        for k in [2, 3] do
          let hint' := ", ".intercalate (List.replicate k hintText)
          unsolved.restore
          let found ← try checkStep hint'; pure true catch _ => pure false
          if found then
            unsolved.restore
            throwError "`{mv.item}` is applied {k} times in this step, so cite it {k} times, \{{hint'}}"
      let msg ← failMessage mv f probe uncited citedItems isImp
      unsolved.restore
      throwError "the step is not justified by {hint}:{indentExpr goalTy}\n{msg}"

  for _ in [0:8] do
    if (← getGoals).isEmpty then break
    unless (← closeByRfl) || (← closeByAC) do break
  if let g :: _ := ← getGoals then
    let ty ← instantiateMVars (← g.getType)
    if plan.size == 1 && !plan[0]!.laws.isEmpty && items.length == 1 then
      for k in [2, 3] do
        let hint' := ", ".intercalate (List.replicate k hintText)
        unsolved.restore
        let found ← try checkStep hint'; pure true catch _ => pure false
        if found then
          unsolved.restore
          throwError "`{plan[0]!.item}` is applied {k} times in this step, so cite it {k} times, \{{hint'}}"
    unsolved.restore
    if let some (l, r) := stepSides ty then
      throwError "the step is not justified by {hint}: the part{indentExpr l}\nis not turned into{indentExpr r}"
    throwError "the step is not justified by {hint}"
  -- Using the surrounding formula or an assumption requires Conditional Substitution.

  if (← sc.usedHyp.get) && !condSubst then
    unsolved.restore
    let hint := ", ".intercalate (["Conditional Substitution"] ++ citedItems ++ moves.toList.map (·.item))
    throwError "the condition of the theorem comes from an assumption or from the line itself, so the step is a conditional substitution, \{{hint}}"

/-! ## Tactics -/

/-- Attach the step goal to its source span. Show no pending goal on `qed`. -/
def showGoal (a b : Nat) (goals : List MVarId) (mctx : MetavarContext) : TacticM Unit := do
  if a == 0 && b == 0 then return
  let stx := Syntax.atom (.synthetic ⟨a⟩ ⟨b⟩ true) "step"
  let ei : ElabInfo := { elaborator := `PT.step, stx := stx }
  let info : TacticInfo := ⟨ei, mctx, goals, mctx, goals⟩
  pushInfoLeaf (.ofTacticInfo info)

syntax (name := ptStepTac) "pt_step " str num num : tactic
@[tactic ptStepTac] def evalPtStep : Tactic := fun stx => withMainContext do
  unless pt.check.get (← getOptions) do
    Lean.Elab.admitGoal (← getMainGoal) (synthetic := true); replaceMainGoal []; return
  let some s := stx[1].isStrLit? | throwError "expected a string"
  let goal ← getMainGoal
  let mctx ← getMCtx
  checkStep s stx[1]
  showGoal stx[2].toNat stx[3].toNat [goal] mctx

syntax (name := lawTac) "law " term,+ : tactic
@[tactic lawTac] def evalLaw : Tactic := fun stx => withMainContext do
  let mut names : Array String := #[]
  for t in stx[1].getSepArgs do
    unless t.isIdent do throwErrorAt t "`law` takes the names of theorems, `law Commutativity`"
    names := names.push t.getId.toString
  checkStep (", ".intercalate names.toList)

partial def proofOf (leaves : Array (Expr × Expr)) (a : Expr) : MetaM (Option Expr) := do
  for (pf, ty) in leaves do
    if ← isDefEq ty a then return some pf
  if let some (x, y) := a.app2? ``And then
    if let some px ← proofOf leaves x then
      if let some py ← proofOf leaves y then
        return some (mkApp4 (mkConst ``And.intro) x y px py)
  return none

syntax (name := ptAssumeTac) "pt_assume " "[" term,* "]" : tactic
@[tactic ptAssumeTac] def evalPtAssume : Tactic := fun stx => withMainContext do
  let terms : Array Term := stx[2].getSepArgs.map (⟨·⟩)
  let goalTy ← instantiateMVars (← (← getMainGoal).getType)
  let some (ant, _) := goalTy.app2? ``PT.Imp
    | throwError "`assume` needs a statement of the form `A ⇒ B`. The assumptions are the conjuncts of `A`"
  evalTactic (← `(tactic| refine fun h => ?_))
  let goal ← getMainGoal
  let h := (← goal.getDecl).lctx.lastDecl.get!
  let leaves := andLeaves (mkFVar h.fvarId) ant
  let mut hyps : Array Hypothesis := #[]
  for t in terms do
    let a ← Tactic.elabTerm t (some (mkSort Level.zero))
    let some pf ← proofOf leaves a
      | throwErrorAt t "`{a}` is not a conjunct of the antecedent{indentExpr ant}"
    hyps := hyps.push { userName := Name.mkSimple s!"h{hyps.size + 1}", type := a, value := pf }
  let (_, goal) ← goal.assertHypotheses hyps
  let goal ← goal.tryClear h.fvarId
  replaceMainGoal [goal]

syntax (name := ptUnprovedTac) "pt_unproved" : tactic
@[tactic ptUnprovedTac] def evalPtUnproved : Tactic := fun _ => do
  Lean.Elab.admitGoal (← getMainGoal) (synthetic := true)
  replaceMainGoal []

def proveAC (a b : Expr) : TacticM Expr := do
  unless acNorm a == acNorm b do throwError "not equal up to AC"
  let h ← mkFreshExprMVar (← mkEq a b)
  let gs ← getGoals
  try
    setGoals [h.mvarId!]
    evalTactic (← `(tactic| pt_ac))
    unless (← getUnsolvedGoals).isEmpty do throwError "not equal up to AC"
    setGoals gs
  catch e => setGoals gs; throw e
  return h

syntax (name := ptConcludeTac) "pt_conclude " num num term : tactic
@[tactic ptConcludeTac] def evalPtConclude : Tactic := fun stx => withMainContext do
  let goal ← getMainGoal
  let goalTy ← instantiateMVars (← goal.getType)
  let mctx ← getMCtx
  let e ← Tactic.elabTerm stx[3] none
  -- An earlier error leaves `sorry` in the chain, so the proof remains unfinished.
  let broken := (← instantiateMVars e).hasSorry
  let ty ← instantiateMVars (← inferType e)
  unless pt.check.get (← getOptions) do
    Lean.Elab.admitGoal goal (synthetic := true); replaceMainGoal []; return

  let fit (ty e : Expr) : TacticM Bool := do
    if ← isDefEq ty goalTy then
      goal.assign e; return true
    let tT := mkApp2 (mkConst ``Iff) goalTy (mkConst ``PT.T)
    if ← isDefEq ty tT then
      goal.assign (mkApp2 (mkConst ``PT.of_equiv_T) goalTy e); return true
    let tT' := mkApp2 (mkConst ``Iff) (mkConst ``PT.T) goalTy
    if ← isDefEq ty tT' then
      goal.assign (mkApp2 (mkConst ``PT.of_equiv_T) goalTy (mkApp3 (mkConst ``Iff.symm) (mkConst ``PT.T) goalTy e))
      return true
    let impT := mkApp2 (mkConst ``PT.Imp) (mkConst ``PT.T) goalTy
    if ← isDefEq ty impT then
      goal.assign (mkApp2 (mkConst ``PT.of_imp_T) goalTy e); return true
    if let some (a, b) := goalTy.app2? ``PT.Imp then
      if ← isDefEq ty (mkApp2 (mkConst ``Iff) a b) then
        goal.assign (mkApp3 (mkConst ``PT.Imp.of_iff) a b e); return true
    if let some (a, b) := goalTy.iff? then
      if ← isDefEq ty (mkApp2 (mkConst ``Iff) b a) then
        goal.assign (mkApp3 (mkConst ``Iff.symm) b a e); return true
    if let some (_, a, b) := goalTy.eq? then
      if ← isDefEq ty (← mkEq b a) then
        goal.assign (← mkEqSymm e); return true
    return false
  let accomplished : TacticM Unit := do
    replaceMainGoal []
    unless broken do showGoal stx[1].toNat stx[2].toNat [] mctx
  if ← fit ty e then accomplished; return

  let mut cands := #[goalTy, mkApp2 (mkConst ``Iff) goalTy (mkConst ``PT.T),
    mkApp2 (mkConst ``Iff) (mkConst ``PT.T) goalTy, mkApp2 (mkConst ``PT.Imp) (mkConst ``PT.T) goalTy]
  if let some (a, b) := goalTy.app2? ``PT.Imp then cands := cands.push (mkApp2 (mkConst ``Iff) a b)
  if let some (a, b) := goalTy.iff? then cands := cands.push (mkApp2 (mkConst ``Iff) b a)
  for cand in cands do
    let s ← saveState
    try
      let eq ← proveAC ty cand
      let e' := mkApp4 (mkConst ``PT.of_ac) ty cand e eq
      if ← fit cand e' then accomplished; return
    catch _ => pure ()
    s.restore
  let hint := if goalTy.isAppOfArity ``Iff 2 || goalTy.isAppOfArity ``Eq 3 then m!""
    else m!"\nA statement that is not an equation is proved by calculating it down to `T`, or with `assume` (see the README)"
  throwError "the calculation proves{indentExpr ty}\nbut the statement is{indentExpr goalTy}{hint}"

/-! ## Strict mode -/

private def allowedTacticKinds : List Name :=
  [ ``lawTac, ``ptStepTac, ``ptConcludeTac, ``ptAssumeTac, ``ptUnprovedTac, ``Lean.calcTactic,
    ``Lean.Parser.Tactic.tacticSeq, ``Lean.Parser.Tactic.tacticSeq1Indented,
    ``Lean.Parser.Tactic.tacticSeqBracketed, ``Lean.Parser.Tactic.tacticSorry,
    ``Lean.Parser.Tactic.paren ]

private def allowedProofKinds : List Name :=
  [ ``Lean.Parser.Term.byTactic, ``Lean.calc, ``Lean.Parser.Term.sorry ]

private def checkProofTerm (report : Syntax → MessageData → CommandElabM Unit) (t : Syntax) : CommandElabM Unit := do
  unless allowedProofKinds.contains t.getKind do
    report t m!"not allowed in strict mode, a proof must be `by law ...` or a `calc` block (found `{t.getKind}`)"

private def checkTactic (report : Syntax → MessageData → CommandElabM Unit) (t : Syntax) : CommandElabM Unit := do
  if t.isAtom || t.getKind == nullKind then return
  unless allowedTacticKinds.contains t.getKind do
    report t m!"tactic `{t.getKind}` is not allowed in strict mode, justify the step with `law <theorem>`"

private partial def visit (report : Syntax → MessageData → CommandElabM Unit) (inThm : Bool) (s : Syntax) : CommandElabM Unit := do
  match s with
  | .node _ k args =>
    let inThm := inThm || k == ``Lean.Parser.Command.theorem || k == ``Lean.Parser.Command.example
    if k == ``Lean.Parser.Tactic.tacticSeq1Indented then
      args[0]!.getArgs.forM (checkTactic report)
    if k == ``Lean.Parser.Tactic.tacticSeqBracketed then
      args[1]!.getArgs.forM (checkTactic report)
    if inThm && k == ``Lean.calcStep then
      checkProofTerm report args[2]!
    if inThm && k == ``Lean.calcFirstStep then
      if args[1]!.getNumArgs > 0 then checkProofTerm report args[1]![1]!
    if inThm && k == ``Lean.Parser.Command.declValSimple then
      checkProofTerm report args[1]!
    for a in args do visit report inThm a
  | _ => pure ()

private def allowedCommandKinds : List Name :=
  [ ``Lean.Parser.Command.declaration, ``Lean.Parser.Command.open, ``Lean.Parser.Command.set_option,
    ``Lean.Parser.Command.in, ``Lean.Parser.Command.moduleDoc, ``Lean.Parser.Command.check,
    ``Lean.guardMsgsCmd,
    ``Lean.Parser.Command.namespace, ``Lean.Parser.Command.section, ``Lean.Parser.Command.end,
    ``Lean.Parser.Command.eoi ]

/-- Enforce the allowed command subset. -/
private partial def checkCommand (report : Syntax → MessageData → CommandElabM Unit) (stx : Syntax) : CommandElabM Unit := do
  let k := stx.getKind
  if k == ``Lean.Parser.Command.in then
    checkCommand report stx[2]
  else if k == ``Lean.Parser.Command.declaration then
    let d := stx[1]
    unless d.getKind == ``Lean.Parser.Command.theorem || d.getKind == ``Lean.Parser.Command.example do
      report stx m!"`{d.getKind}` is not allowed in strict mode, write a `proof`"

    if let some id := d.find? (·.getKind == ``Lean.Parser.Command.declId) then
      if id[0].getId.components.any (·.toString.startsWith "_") then
        report id m!"a name may not start with `_`"
    if let some v := stx[0].find? (·.getKind == ``Lean.Parser.Command.private) then
      report v m!"`private` is not allowed in strict mode"
    if let some w := d.find? (·.getKind == ``Lean.Parser.Term.whereDecls) then
      report w m!"`where` is not allowed in strict mode"
  else if k == ``Lean.guardMsgsCmd then
    -- `strictScan` checks inside `#guard_msgs`, which the linter skips.

    report stx m!"`#guard_msgs` hides messages, it is not allowed in strict mode"
    checkCommand report stx[stx.getNumArgs - 1]
  else if !allowedCommandKinds.contains k && !(`PT).isPrefixOf k then
    report stx m!"`{k}` is not allowed in strict mode"

def strictLinter : Linter where
  name := `pt.strict
  run stx := do
    unless pt.strict.get (← getOptions) do return
    checkCommand (fun stx msg => logErrorAt stx msg) stx
    visit (fun stx msg => logErrorAt stx msg) false stx

/-- Reparse the file to catch commands hidden from the linter by `#guard_msgs`. -/
def strictScan : CommandElabM (Array String) := do
  if pt.tests.get (← getOptions) then return #[]
  let src := (← getFileMap).source
  let ictx := Parser.mkInputContext src (← getFileName)
  let (_, pstate, _) ← Parser.parseHeader ictx
  let pmctx : Parser.ParserModuleContext := { env := ← getEnv, options := ← getOptions }
  let found ← IO.mkRef (#[] : Array String)
  let report (stx : Syntax) (msg : MessageData) : CommandElabM Unit := do
    let line := ((← getFileMap).toPosition (stx.getPos?.getD 0)).line
    found.modify (·.push s!"line {line}: {← msg.toString}")
  let mut pstate := pstate
  let mut msgs : MessageLog := {}
  repeat
    let (stx, pstate', msgs') := Parser.parseCommand ictx pmctx pstate msgs
    pstate := pstate'
    msgs := msgs'
    if stx.isOfKind ``Parser.Command.eoi then break
    checkCommand report stx
    visit report false stx
  found.get

initialize addLinter strictLinter

end PT
