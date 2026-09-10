import Lean
import PT.Syntax

open Lean Elab Command

set_option pt.strict false

namespace PT

syntax (name := appendixCmd) "appendix " num "-" num : command

@[command_elab appendixCmd] def elabAppendix : CommandElab := fun stx => do
  unless stx[1].toNat == 1 do throwErrorAt stx[1] "the sections start at 1"
  let hi := stx[3].toNat
  modifyScope fun sc => { sc with opts := pt.sections.set sc.opts hi }
  modifyEnv (appendixExt.setState · (some hi))

syntax (name := statusCmd) "status" : command

@[command_elab statusCmd] def elabStatus : CommandElab := fun _ => do
  let env ← getEnv
  let mut proved : Array Name := #[]
  let mut open_ : Array Name := #[]
  let mut flagged : Array Name := #[]

  let mut other : Array Name := #[]
  let mut axiomatic : Array Name := #[]

  let mut relaxed : Array Name := #[]
  let mut wrong : Array Name := #[]

  let mut anonProved : Nat := 0
  let mut anonOpen : Nat := 0
  let mut anonFlagged : Nat := 0
  for (n, ci) in env.constants.map₂.toList do
    unless ci.isTheorem do continue
    if n.isInternal then continue
    let check ← checkProof n
    unless check.block do other := other.push n
    if check.relaxed then relaxed := relaxed.push n
    if check.axiomatic then axiomatic := axiomatic.push n
    unless check.matchesObligation do wrong := wrong.push n
    if anonTag.hasTag env n then
      if !check.complete then anonOpen := anonOpen + 1
      else if check.issue?.isSome then anonFlagged := anonFlagged + 1
      else anonProved := anonProved + 1
      continue
    if !check.complete then open_ := open_.push n
    else if check.issue?.isSome then flagged := flagged.push n
    else proved := proved.push n
  let sorted (a : Array Name) := a.qsort (fun x y => x.toString < y.toString)
  let line (label : String) (a : Array Name) : MessageData :=
    if a.isEmpty then m!"{label} (0)"
    else m!"{label} ({a.size}) {", ".intercalate ((sorted a).toList.map toString)}"
  let mut msg := line "proved" proved ++ m!"\n" ++ line "not proved" open_
  unless flagged.isEmpty do msg := msg ++ m!"\n" ++ line "flagged" flagged
  if anonProved + anonOpen + anonFlagged > 0 then
    msg := msg ++ m!"\nunnamed proofs: {anonProved} proved, {anonOpen} not proved"
    if anonFlagged > 0 then msg := msg ++ m!", {anonFlagged} flagged"
  unless pt.check.get (← getOptions) do
    msg := m!"checking is currently off (pt.check); proofs written with checking off are not proved\n" ++ msg
  unless other.isEmpty do msg := msg ++ m!"\n" ++ line "not written as proof blocks" other
  unless axiomatic.isEmpty do msg := msg ++ m!"\n" ++ line "resting on axioms of this file" axiomatic
  unless relaxed.isEmpty do msg := msg ++ m!"\n" ++ line "checked with weakened options" relaxed
  unless wrong.isEmpty do msg := msg ++ m!"\n" ++ line "not the stated program obligation" wrong

  let mut obligations : Array Name := #[]
  for (n, ci) in env.constants.map₂.toList do
    unless n.getString! == "ob" && ci.isDefinition do continue
    let th := n.getPrefix
    if (← checkProof th).issue?.isSome then obligations := obligations.push th
  unless obligations.isEmpty do msg := msg ++ m!"\n" ++ line "obligations not verified" obligations
  if pt.tests.get (← getOptions) then
    msg := m!"pt.tests is set, `#guard_msgs` may hide messages and the strict rules are not scanned\n" ++ msg
  let broken ← strictScan
  unless broken.isEmpty do
    msg := m!"not in strict mode, the report may be incomplete\n  {"\n  ".intercalate broken.toList}\n" ++ msg
  logInfo msg

end PT
