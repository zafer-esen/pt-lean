import Lean
import PT.Hints

open Lean Server Lsp

set_option pt.strict false

namespace PT

def hintItems (range : Range) (maxSec : Nat := 0) : Array CompletionItem := Id.run do
  let mut out := #[]
  let mk (label detail : String) (kind : CompletionItemKind) (sort : Nat) : CompletionItem :=
    { label, detail? := some detail, kind? := some kind,
      sortText? := some (toString (100 + sort)),      -- keep appendix order
      textEdit? := some { newText := label, insert := range, replace := range } }
  for e in hintTable, i in [0:hintTable.length] do
    unless inSections maxSec e do continue
    out := out.push (mk e.name e.number .constant (3 * i))
    if e.number != "" then out := out.push (mk e.number e.name .value (3 * i + 1))
    for a in e.aliases do out := out.push (mk a s!"= {e.name}" .constant (3 * i + 2))
  out := out.push (mk "Arithmetic" "an arithmetic fact (Arithmetic: m ≤ m + 1)" .keyword 998)
  out := out.push (mk "Assumption" "an assumption of the proof (Assumption: p)" .keyword 999)
  out := out.push (mk "Conditional Substitution" "a theorem whose condition an assumption supplies" .keyword 999)
  return out

def linePrefix (text : FileMap) (pos : Lsp.Position) : String :=
  let lineStart := text.positions[pos.line]?.getD ⟨0⟩
  String.Pos.Raw.extract text.source lineStart (text.lspPosToUtf8Pos pos)

/-- Complete the last comma-separated item, except after its formula-selecting colon. -/
def currentItem (typed : String) : Option String := Id.run do
  let mut depth := 0
  let mut item : List Char := []
  for c in typed.toList do
    if c == '(' || c == '[' then depth := depth + 1
    else if c == ')' || c == ']' then depth := depth - 1
    if c == ',' && depth == 0 then item := [] else item := item ++ [c]
  let cur := item.dropWhile (· == ' ')
  if cur.contains ':' then none else some (String.ofList cur)

def hintCompletion (p : CompletionParams) (prev : RequestTask CompletionList)
    : RequestM (RequestTask CompletionList) := do
  let text := (← RequestM.readDoc).meta.text
  let line := linePrefix text p.position
  let parts := line.splitOn "{"
  if parts.length < 2 then return prev
  let typed := parts.getLast!
  let before := ("{".intercalate parts.dropLast).trimAscii.toString
  unless (before.endsWith "=" && !before.endsWith ":=") || before.endsWith "⇒" do return prev
  if typed.any (· == '}') then return prev
  let some item := currentItem typed | return prev
  let start := { p.position with character := p.position.character - item.length }

  RequestM.withWaitFindSnapAtPos p.position fun snap => do
    let maxSec := pt.sections.get snap.cmdState.scopes.head!.opts
    return { isIncomplete := false, items := hintItems ⟨start, p.position⟩ maxSec }

end PT

initialize
  chainLspRequestHandler "textDocument/completion" CompletionParams CompletionList PT.hintCompletion
