import Prismriver.Repr.Classical
import Prismriver.Repr.Score
import Lean.Elab

namespace Prismriver.Syntax

open Lean Prismriver.Classical

private meta def syntaxInt (n : Int) : MacroM (TSyntax `term) := do
  match n with
  | .ofNat n => `(Int.ofNat $(Syntax.mkNumLit <| toString n))
  | .negSucc n => `(Int.negSucc $(Syntax.mkNumLit <| toString n))

declare_syntax_cat music_note

abbrev hepKind : SyntaxNodeKind := `hep
def hepFn : Parser.ParserFn :=
  Parser.nodeFn hepKind <|
  Parser.rawFn (trailingWs := true) fun ctx s =>
    let slice := ctx.substring s.pos ctx.endPos
    let slice' := slice.dropWhile ("abcdefg".contains ·)
    if slice == slice' then
      s.mkErrorsAt [""] s.pos
    else
      s.setPos slice'.startPos

def hepNoAntiquot : Parser.Parser where
  fn := hepFn

open PrettyPrinter Formatter in
@[combinator_formatter hepNoAntiquot]
def hepNoAntiquot.formatter : Formatter :=
  visitAtom hepKind

open PrettyPrinter Parenthesizer in
@[combinator_parenthesizer hepNoAntiquot]
def hepNoAntiquot.parenthesizer : Parenthesizer := visitToken

/-- Parser which eats a hep -/
def hep := Parser.withAntiquot (Parser.mkAntiquot "hep" hepKind) hepNoAntiquot

def markSharp : List Char := ['s', '♯']
def markFlat : List Char := ['f', '♭']

abbrev accidentalKind : SyntaxNodeKind := `accidental
def accidentalNoAntiquot : Parser.Parser where
  fn := Parser.nodeFn accidentalKind <|
    Parser.rawFn (trailingWs := true) fun ctx s =>
      let slice := ctx.substring s.pos ctx.endPos
      let slice' := slice.dropWhile (λ ch => markSharp.contains ch || markFlat.contains ch)
      if slice == slice' then
        s.mkErrorsAt [""] s.pos
      else
        s.setPos slice'.startPos
open PrettyPrinter Formatter in
@[combinator_formatter accidentalNoAntiquot]
def accidentalNoAntiquot.formatter : Formatter :=
  visitAtom accidentalKind
open PrettyPrinter Parenthesizer in
@[combinator_parenthesizer accidentalNoAntiquot]
def accidentalNoAntiquot.parenthesizer : Parenthesizer := visitToken
def accidental := Parser.withAntiquot (Parser.mkAntiquot "accidental" accidentalKind) accidentalNoAntiquot

def markOctaveUp : Char := '\''
def markOctaveDown : Char := ','

abbrev octaveKind : SyntaxNodeKind := `octave
def octaveNoAntiquot : Parser.Parser where
  fn := Parser.nodeFn octaveKind <|
    Parser.rawFn (trailingWs := true) fun ctx s =>
      let slice := ctx.substring s.pos ctx.endPos
      let slice' := slice.dropWhile (λ ch => ch == markOctaveUp || ch == markOctaveDown)
      if slice == slice' then
        s.mkErrorsAt [""] s.pos
      else
        s.setPos slice'.startPos
open PrettyPrinter Formatter in
@[combinator_formatter octaveNoAntiquot]
def octaveNoAntiquot.formatter : Formatter :=
  visitAtom octaveKind
open PrettyPrinter Parenthesizer in
@[combinator_parenthesizer octaveNoAntiquot]
def octaveNoAntiquot.parenthesizer : Parenthesizer := visitToken
def octave := Parser.withAntiquot (Parser.mkAntiquot "octave" octaveKind) octaveNoAntiquot

abbrev dottedKind : SyntaxNodeKind := `dotted
def dottedNoAntiquot : Parser.Parser where
  fn := Parser.nodeFn dottedKind <|
    Parser.rawFn (trailingWs := true) fun ctx s =>
      let slice := ctx.substring s.pos ctx.endPos
      let slice' := slice.dropWhile (· == '.')
      if slice == slice' then
        s.mkErrorsAt [""] s.pos
      else
        s.setPos slice'.startPos
open PrettyPrinter Formatter in
@[combinator_formatter dottedNoAntiquot]
def dottedNoAntiquot.formatter : Formatter :=
  visitAtom dottedKind
open PrettyPrinter Parenthesizer in
@[combinator_parenthesizer dottedNoAntiquot]
def dottedNoAntiquot.parenthesizer : Parenthesizer := visitToken
def dotted := Parser.withAntiquot (Parser.mkAntiquot "dotted" dottedKind) dottedNoAntiquot

-- A music note is a pitch plus an optional duration
syntax hep optional(noWs accidental) optional(noWs octave) optional(noWs num optional(noWs dotted)) : music_note

declare_syntax_cat music_seq
syntax music_note* : music_seq

def mapNote (stx : TSyntax `music_note) : MacroM Term := do
  let `(music_note| $h:hep$[$acc?:accidental]?$[$oct?:octave]?$[$d?:num$[$dotted?:dotted]?]?) := stx
    | Macro.throwError "Invalid note"
  let h' := (h.raw.isLit? hepKind).getD "c"
  let acc := acc?.bind (·.raw.isLit? accidentalKind) |>.getD ""
  let oct := oct?.bind (·.raw.isLit? octaveKind) |>.getD ""
  let dots := dotted?.join.bind (·.raw.isLit? dottedKind) |>.getD "" |>.length
  let duration := (2 - mkRat 1 (2 ^ dots)) /(d?.map (·.getNat) |>.getD 4)
  let pitch ← parsePitch h' acc oct
  `(term|Note.mk $pitch (mkRat $(Syntax.mkNumLit <| toString duration.num) $(Syntax.mkNumLit <| toString duration.den) : MeasuredTime))
  where
  parsePitch (p acc oct : String) : MacroM Term := do
    let acc : Int := acc.foldl (init := 0)
        λ acc ch => match ch with
          | 's' => acc + 1
          | 'f' => acc - 1
          | _ => acc
    let oct : Int := oct.foldl (init := 0)
        λ acc ch => match ch with
          | '\'' => acc + 1
          | ',' => acc - 1
          | _ => acc
    let hep := mkIdent s!"Hep.{p}".toName
    let acc ← syntaxInt acc
    let oct ← syntaxInt oct
    `(term|Pitch.new $hep $oct ⟨$acc⟩)

syntax (name := music) "♩[" music_seq "]" : term

macro_rules
  | `(♩[ $seq:music_seq ]) => do
    let `(music_seq|$notes:music_note*) := seq
      | Macro.throwError "Must be a sequence of notes"
    let notes ← notes.mapM mapNote
    let content :=  Syntax.TSepArray.ofElems notes
    `(term|[$(content),*])


example : ♩[ c4 ] == [ (⟨.new .c 0, 0, mkRat 1 4⟩ : @Classical.Note) ] := by decide
example : ♩[ d4.. ] == [ (⟨.new .d 0, 0, mkRat 7 16⟩ : @Classical.Note) ] := by decide
#eval (♩[ cs5 d4.. e f ] : List @Classical.Note)
#eval (♩[ c'' d e f5 ] : List @Classical.Note)
#eval (♩[ c,,,, d e f5 ] : List @Classical.Note)

def play (aldaCode : String) : IO UInt32 := do
  let lockFile := "/tmp/prismriver-alda.lock"
  let hLock ← IO.FS.Handle.mk lockFile .write
  let flag ← hLock.tryLock
  if !flag then
    return 0
  let ch ← IO.Process.spawn { cmd := "alda", args := #["play", "--wait", "--code", aldaCode] }
  let ret ← ch.wait
  hLock.unlock
  return ret

elab "#play" e:term : command => do
  let notes ← Elab.Command.liftTermElabM do
    let type ← Elab.Term.elabType (← `(term|List Prismriver.Classical.Note))
    let li ← Elab.Term.elabTerm e (.some type)
    let notes ← unsafe do
      Meta.evalExpr (List Classical.Note) type li
    return notes

  let notes := " ".intercalate $ notes.map λ note =>
    s!"o{note.pitch.octave + 4} {note.pitch.hep}"
  let code := s!"piano: {notes}"

  logInfo s!"{code}"
  let ret ← play code
  if ret ≠ 0 then
    throwError s!"Subprocess failed: {ret}"
