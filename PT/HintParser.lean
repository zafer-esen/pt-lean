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

end PT

initialize register_parser_alias (kind := `PT.hintText) "hintText" PT.hintText
