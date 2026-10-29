import Lean

open Lean Parser PrettyPrinter

namespace PT

def hintTextKind : SyntaxNodeKind := `PT.hintText

def hintTextFn : ParserFn := fun c s =>
  let startPos := s.pos
  let s := takeUntilFn (fun ch => ch == '}' || ch == '\n') c s
  mkNodeToken hintTextKind startPos true c s

def hintText : Parser := { fn := hintTextFn }

@[combinator_formatter hintText] def hintText.formatter : Formatter := Formatter.visitAtom hintTextKind
@[combinator_parenthesizer hintText] def hintText.parenthesizer : Parenthesizer := Parenthesizer.visitToken

/-- Hint text that does not start as an annotation `{R : …}`, which may follow it. -/
def callHintFn : ParserFn := fun c s =>
  let name := takeWhileFn (fun ch => ch.isAlphanum || ch == '_' || ch == '\'') c s
  let colon := takeWhileFn (· == ' ') c name
  if name.pos != s.pos && !c.atEnd colon.pos && c.get colon.pos == ':' then
    s.mkErrorAt "the theorems by which the triple is obtained" s.pos
  else hintTextFn c s

def callHintText : Parser := { fn := callHintFn }

@[combinator_formatter callHintText] def callHintText.formatter : Formatter := Formatter.visitAtom hintTextKind
@[combinator_parenthesizer callHintText] def callHintText.parenthesizer : Parenthesizer := Parenthesizer.visitToken

end PT

initialize register_parser_alias (kind := `PT.hintText) "hintText" PT.hintText
initialize register_parser_alias (kind := `PT.hintText) "callHintText" PT.callHintText
