import PT.Program

open Lean Elab Command Meta

set_option pt.strict false

namespace PT

syntax ptCallHint := atomic("{" callHintText "}")
/-- A call with its triple `{Q'} P() {R'}` and the theorems by which it is obtained. -/
syntax (name := ptCall) atomic(ptAnnot ident noWs "(" ")") ptAnnot (ptCallHint)? : ptcmd
syntax (name := ptCallBare) atomic(ident noWs "(" ")") : ptcmd

syntax ptBound := atomic("{" &"bound") ident " : " ptf "}"
syntax (name := procCmd) "proc " ident ptAnnot (ptBound)? ptcmd ptAnnot : command

macro_rules
  | `(⟦ $c:ptcmd ⟧) => do
    unless c.raw.getKind == ``ptCall || c.raw.getKind == ``ptCallBare do Macro.throwUnsupported
    Macro.throwErrorAt c "a call has no wp. In the obligations of `proc`, the body is split at the call"

private def isCall (S : Syntax) : Bool := S.getKind == ``ptCall || S.getKind == ``ptCallBare

private partial def seqItems (S : Syntax) : Array Syntax :=
  if S.getKind == ``PT.«ptcmd_;_» then seqItems S[0] ++ seqItems S[2] else #[S]

private def seqOf (items : Array Syntax) : MacroM (Option (TSyntax `ptcmd)) := do
  let some last := items.back? | return none
  some <$> items.pop.foldrM (init := (⟨last⟩ : TSyntax `ptcmd)) fun a acc => `(ptcmd| $(⟨a⟩):ptcmd; $acc)

/-- A command `S₁; P(); S₂` with its triple `{Q'} P() {R'}`. -/
structure CallSite where
  pre : Option (TSyntax `ptcmd)
  call : Syntax
  post : Option (TSyntax `ptcmd)

private def splitAtCall (S : Syntax) : CommandElabM (Option CallSite) := do
  let items := seqItems S
  for it in items do
    unless isCall it do
      if let some c := it.find? isCall then
        throwErrorAt c "a call is supported only as a command of the body or of a branch of its outer `if`, as in `S₁; P(); S₂`"
  let some i := items.findIdx? isCall | return none
  if let some c := (items.extract (i + 1) items.size).find? isCall then
    throwErrorAt c "only one call per branch is supported"
  return some {
    pre := ← liftMacroM (seqOf (items.extract 0 i))
    call := items[i]!
    post := ← liftMacroM (seqOf (items.extract (i + 1) items.size)) }

/-- The state variables in `stx`, outside the annotations of calls. -/
private partial def stateVars (fields : Array Name) (stx : Syntax) : Array Name :=
  if stx.getKind == ``ptCall then #[]
  else if stx.isIdent && fields.contains stx.getId then #[stx.getId]
  else stx.getArgs.flatMap (stateVars fields)

private def callTheorems : List String :=
  ["Substitution Theorem II", "Substitution Theorem I", "Invariance Theorem", "Conjunction Theorem"]

/-- The cited items `Theorem: argument`, split at each comma before a theorem. -/
private def citedTheorems (hint : String) : Array String :=
  (hint.splitOn ",").foldl (init := #[]) fun acc piece =>
    let item := piece.trimAscii.toString
    if acc.isEmpty || callTheorems.any fun n => item.startsWith n then acc.push item
    else acc.modify (acc.size - 1) (· ++ "," ++ piece)

private def parseArg (cat : Name) (text : String) : CommandElabM (Option Syntax) := do
  match Parser.runParserCategory (← getEnv) cat text with
  | .ok s => return some (noPositions s)
  | .error _ => return none

/-- `{Q'} P() {R'}` as obtained from `{Q} P() {R}` by the theorems cited after it. -/
private def callTriple (procId : Ident) (fields varsP : Array Name) (Q R : TSyntax `ptf) (call : Syntax) :
    CommandElabM (TSyntax `ptf × TSyntax `ptf) := do
  let callee := if call.getKind == ``ptCall then call[1] else call[0]
  unless callee.getId == procId.getId do
    throwErrorAt callee "only calls of `{procId.getId}` itself are supported"
  if call.getKind == ``ptCallBare then return (Q, R)
  let Q' : TSyntax `ptf := ⟨call[0][3]⟩
  let R' : TSyntax `ptf := ⟨call[4][3]⟩
  let hint? := if call[5].getNumArgs > 0 then some call[5][0] else none
  let P := procId.getId
  let mut steps : Array (String × Syntax) := #[]
  if let some h := hint? then
    for item in citedTheorems h[1][0].getAtomVal do
      let some thm := callTheorems.find? fun n => item.startsWith n |
        throwErrorAt h "`{item}` is not a theorem about calls. Cite Substitution Theorem I or II, or the Invariance Theorem with the Conjunction Theorem"
      let arg := String.ofList ((item.toList.drop thm.length).dropWhile (· == ' ') |>.dropWhile (· == ':'))
      let arg := arg.trimAscii.toString
      let some s ← (if thm == "Invariance Theorem" then parseArg `ptf arg
          else if thm == "Conjunction Theorem" then pure (if arg.isEmpty then some .missing else none)
          else parseArg `ptcmd arg) |
        throwErrorAt h (if thm == "Invariance Theorem" then "write the formula that is kept by the Invariance Theorem, e.g., {Invariance Theorem: x = X}"
          else if thm == "Conjunction Theorem" then "the Conjunction Theorem is cited without an argument"
          else s!"write the substitution as an assignment, e.g., \{{thm}: y := e}")
      if thm.startsWith "Substitution" && s.getKind != ``ptAssignCmd then
        throwErrorAt h s!"write the substitution as an assignment, e.g., \{{thm}: y := e}"
      steps := steps.push (thm, s)
  let some st ← liftTermElabM stateName? | throwErrorAt procId "declare the program variables with `state` first"
  let elabF (f : Syntax) (formula := true) : TermElabM Expr := do
    let e ← Term.elabTerm (← `(⟪$(⟨f⟩):ptf⟫)) (if formula then some (mkSort .zero) else none)
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let varsOf (e : Expr) : Array Name := fields.filter fun f =>
    (e.find? (·.isAppOf (st ++ f))).isSome
  let equal (a b : Expr) : TermElabM Bool := do
    if ← sameFormula a b then return true
    equalByArith a b
  liftTermElabM <| withLocalDeclD `σ (mkConst st) fun σ => do
    let mut A ← elabF Q
    let mut B ← elabF R
    let mut kept : Option Expr := none
    let some h := hint? | do
      unless (← equal A (← elabF Q')) && (← equal B (← elabF R')) do
        throwErrorAt call[4] "this triple is not \{Q} {P}() \{R}. Cite the theorems by which it is obtained in braces right after R', e.g., `\{R' : …} \{Substitution Theorem I: y := e}` or `\{R' : …} \{Invariance Theorem: F, Conjunction Theorem}`"
      return (Q', R')
    for (thm, s) in steps do
      if kept.isSome && thm != "Conjunction Theorem" then
        throwErrorAt h "a second triple is obtained by the Invariance Theorem. Cite the Conjunction Theorem right after the Invariance Theorem"
      if thm.startsWith "Substitution" then
        let xs := s[0].getSepArgs
        let es := s[2].getSepArgs
        for x in xs do
          unless fields.contains x.getId do throwErrorAt h "`{x.getId}` is not a program variable"
          if varsP.contains x.getId then
            throwErrorAt h "`{x.getId}` is a variable of {P}, so it cannot be replaced by {thm}"
          if thm == "Substitution Theorem II" && (varsOf B).contains x.getId then
            throwErrorAt h "`{x.getId}` occurs in the postcondition, so it cannot be replaced by Substitution Theorem II"
        if thm == "Substitution Theorem I" then
          for e in es do
            if let some v := (stateVars fields e).find? varsP.contains then
              throwErrorAt h m!"`{← elabF e false}` contains `{v}`, a variable of {P}, so Substitution Theorem I does not apply"
        let ids : Array Ident := xs.map (⟨·⟩)
        let vals ← es.mapM fun e => `(⟪$(⟨e⟩):ptf⟫)
        let f ← Term.elabTerm (← `(pt_assign% [$ids,*] [$vals,*])) none
        Term.synthesizeSyntheticMVarsNoPostponing
        let updated := (mkApp (← instantiateMVars f) σ).headBeta
        A ← reduceFields (A.replaceFVar σ updated)
        if thm == "Substitution Theorem I" then B ← reduceFields (B.replaceFVar σ updated)
      else if thm == "Invariance Theorem" then
        if let some v := (stateVars fields s).find? varsP.contains then
          throwErrorAt h "`{v}` is a variable of {P}, so this formula is not kept by the Invariance Theorem"
        kept := some (← elabF s)
      else
        let some F := kept | throwErrorAt h "for the Conjunction Theorem, a second triple is needed, e.g., from the Invariance Theorem cited before it"
        A := mkAnd A F
        B := mkAnd B F
        kept := none
    if kept.isSome then
      throwErrorAt h "a second triple is obtained by the Invariance Theorem. Cite the Conjunction Theorem right after the Invariance Theorem"
    unless ← equal A (← elabF Q') do
      throwErrorAt call[0] m!"the precondition obtained by the theorems cited is `{A}`, and Q' is not equal to it by arithmetic"
    unless ← equal B (← elabF R') do
      throwErrorAt call[4] m!"the postcondition obtained by the theorems cited is `{B}`, and R' is not equal to it by arithmetic"
    return (Q', R')

/-- The code before and after the call, `S₁; P(); S₂` as in the Recursion Theorem, or `Sᵢ,₁; P(); Sᵢ,₂` in branch `i`. -/
private def codeAroundCall (guarded : Bool) (i : Nat) : String × String :=
  if guarded then (s!"S{subscript i},₁", s!"S{subscript i},₂") else ("S₁", "S₂")

private inductive Branch where
  | plain (S : TSyntax `ptcmd)
  | call (site : CallSite) (Q' R' : TSyntax `ptf)

/-- The Alternative Command Theorem for the outer `if`, the Recursion Theorem at each call, and the termination conditions. -/
private def procObligations (Q R : TSyntax `ptf) (t? : Option (TSyntax `ptf))
    (guards : Option (Array (TSyntax `ptf))) (branches : Array Branch) :
    MacroM (Array (String × TSyntax `ptf × ObRoles)) := do
  let calls := (branches.filter fun | .call .. => true | _ => false).size
  let t1 : TSyntax `ptf ← `(ptf| $(mkIdent `t1):ident)
  let t2 : TSyntax `ptf ← `(ptf| $(mkIdent `t2):ident)
  let mut out := #[]
  if let some Bs := guards then
    out := out.push (← guardsObligation Q Bs)
  for b in branches, i in [1:branches.size + 1] do
    let B? := guards.map (·[i - 1]!)
    match b with
    | .plain S =>
      if let some B := B? then
        out := out.push (← branchObligation Q R B S i)
      else
        out := out.push ("body", ← `(ptf| ($Q) ⇒ wp($S:ptcmd, $R:ptf)),
          { template := "Q ⇒ wp(S, R)", ante := #[rQ], cmdSym := "S", postSym := "R" })
    | .call site Q' R' =>
      let tag (base : String) := if calls == 1 then base else s!"{base}{i}"
      let (sS, sS') := codeAroundCall B?.isSome i
      let (sQ', sR') := if calls == 1 then ("Q'", "R'") else (s!"Q{subscript i}'", s!"R{subscript i}'")
      let anteT := if B?.isSome then s!"Q ∧ B{subscript i}" else "Q"
      let anteR := #[rQ] ++ (if B?.isSome then #[s!"the guard B{subscript i}"] else #[])
      let ante ← match B? with
        | some B => `(ptf| ($Q) ∧ ($B))
        | none => `(ptf| ($Q))
      out := out.push (tag "before", ← match site.pre with
        | some S => do pure (← `(ptf| $ante ⇒ wp($S:ptcmd, $Q':ptf)),
            ({ template := s!"{anteT} ⇒ wp({sS}, {sQ'})", ante := anteR, cmdSym := sS, postSym := sQ' } : ObRoles))
        | none => do pure (← `(ptf| $ante ⇒ ($Q')),
            { template := s!"{anteT} ⇒ {sQ'}", ante := anteR, cons := s!"the precondition {sQ'} of the call" }))
      out := out.push (tag "after", ← match site.post with
        | some S => do pure (← `(ptf| ($R') ⇒ wp($S:ptcmd, $R:ptf)),
            ({ template := s!"{sR'} ⇒ wp({sS'}, R)", ante := #[s!"the postcondition {sR'} of the call"], cmdSym := sS',
               postSym := "R" } : ObRoles))
        | none => do pure (← `(ptf| ($R') ⇒ ($R)),
            { template := s!"{sR'} ⇒ R", ante := #[s!"the postcondition {sR'} of the call"], cons := rR }))
      let some t := t? | continue
      let save ← `(ptcmd| $(mkIdent `t2):ident := $t)
      let (cmd, cmdT) ← match site.pre with
        | some S => do pure (← `(ptcmd| $S:ptcmd; $save:ptcmd), s!"{sS}; t2 := t")
        | none => pure (save, "t2 := t")
      let decF ← match B? with
        | some B => `(ptf| ($Q) ∧ ($t1 = $t) ∧ ($t2 = ($t) - 1) ∧ ($B) ⇒ wp($cmd:ptcmd, $t2 < $t1))
        | none => `(ptf| ($Q) ∧ ($t1 = $t) ∧ ($t2 = ($t) - 1) ⇒ wp($cmd:ptcmd, $t2 < $t1))
      let guardT := if B?.isSome then s!" ∧ B{subscript i}" else ""
      out := out.push (tag "dec", decF,
        { template := s!"Q ∧ t1 = t ∧ t2 = t - 1{guardT} ⇒ wp({cmdT}, t2 < t1)",
          ante := #[rQ, "t1 = t", "t2 = t - 1"] ++ anteR.extract 1 anteR.size, cmdSym := cmdT,
          postSym := "t2 < t1", note := "t is the bound of the procedure" })
  if let some t := t? then
    out := out.push ("bound", ← `(ptf| ($Q) ⇒ 0 < $t),
      { template := "Q ⇒ 0 < t", ante := #[rQ], cons := "0 < t", note := "t is the bound of the procedure" })
  return out.map fun (n, f, r) => (n, f, { r with owner := "proc" })

private def procLegend (P : Name) (guarded : Bool) (branches : Array Branch) : String :=
  let calls := (branches.filter fun | .call .. => true | _ => false).size
  let cmd (i : Nat) := if guarded then s!"S{subscript i}" else "S"
  let splits := branches.zipIdx.toList.filterMap fun (b, i) => match b with
    | .plain _ => none
    | .call site _ _ =>
      let (sS, sS') := codeAroundCall guarded (i + 1)
      some (s!"{cmd (i + 1)} = " ++ (if site.pre.isSome then s!"{sS}; " else "") ++ s!"{P}()" ++
        (if site.post.isSome then s!"; {sS'}" else ""))
  let body := if guarded then
      [", ".intercalate ((List.range branches.size).map fun i => s!"B{subscript (i + 1)} → {cmd (i + 1)}") ++
        " the guarded commands"] ++ splits
    else [(splits.head?.getD "S") ++ " the body"]
  let items := ["Q and R are the pre- and postcondition"] ++
    (if calls > 0 then ["t the bound", "t1 and t2 the bound at the start and at the call"] else []) ++
    body ++
    (if calls == 1 then [s!"\{Q'} {P}() \{R'} the triple of the call"]
     else if calls > 1 then [s!"\{Qᵢ'} {P}() \{Rᵢ'} the triple of the call in branch i"] else [])
  let legend := ", ".intercalate items.dropLast ++ " and " ++ items.getLast!
  let site := if calls == 1 then "the call" else "the call in branch i"
  let rest := if guarded then "in the other branches and after the call" else "after the call"
  if calls == 0 then legend
  else legend ++ s!"\ndec is \{Q ∧ t1 = t ∧ t2 = t - 1} S' \{t2 < t1} up to the call, with S' the body with t2 := t before {site}. Elsewhere, t1 and t2 are not changed, so t2 < t1 holds {rest}"

@[command_elab procCmd] def elabProc : CommandElab := fun stx => do
  if stx.hasMissing then return
  let name : Ident := ⟨stx[1]⟩
  let Q : TSyntax `ptf := ⟨stx[2][3]⟩
  let bound? := if stx[3].getNumArgs > 0 then some stx[3][0] else none
  let t? : Option (TSyntax `ptf) := bound?.map (⟨·[4]⟩)
  let body := stx[4]
  let R : TSyntax `ptf := ⟨stx[5][3]⟩
  let env ← getEnv
  let some st ← liftTermElabM stateName? | throwErrorAt name "declare the program variables with `state` first"
  let fields := (getStructureInfo? env st).elim #[] (·.fieldNames)
  let guards? : Option (Array (TSyntax `ptf × Syntax)) :=
    if body.getKind == ``ptIf || body.getKind == ``ptIfBar then
      some (body[1].getSepArgs.map fun g => (⟨g[0]⟩, g[2]))
    else none
  let parts := guards?.getD #[(⟨.missing⟩, body)]
  let sites ← parts.mapM fun (_, S) => splitAtCall S
  let hasCall := sites.any (·.isSome)
  match bound?, hasCall with
  | none, true => throwErrorAt name "for a procedure with a call, a bound is needed, `\{bound t : …}` after its precondition"
  | some b, false => throwErrorAt b "`{name.getId}` has no call, so no bound is needed"
  | _, _ => pure ()
  if hasCall then
    for part in #[Q.raw, R.raw, body] ++ t?.toArray.map (·.raw) do
      if let some use := reservedUse? env [`t1, `t2] part then
        throwErrorAt use "`{use.getId}` is reserved for the bound at the start of the procedure and at the call, use another name"
    let msg := "declare the bounds as `t1 t2 : Int` in `state`"
    requireIntVar name `t1 msg
    requireIntVar name `t2 msg
  let varsP := stateVars fields body
  let mut branches : Array Branch := #[]
  for (_, S) in parts, site? in sites do
    match site? with
    | none => branches := branches.push (.plain ⟨S⟩)
    | some site =>
      let (Q', R') ← callTriple name fields varsP Q R site.call
      branches := branches.push (.call site Q' R')
  let obs ← liftMacroM (procObligations Q R t? (guards?.map (·.map (·.1))) branches)
  let callAnnots := sites.toList.filterMap (·.bind fun site =>
    if site.call.getKind == ``ptCall then some #[namedAnnotation site.call[0], namedAnnotation site.call[4]] else none)
  defineObligations name.getId obs (procLegend name.getId guards?.isSome branches)
    (#[namedAnnotation stx[2], namedAnnotation stx[5]] ++ callAnnots.toArray.flatten)

end PT
