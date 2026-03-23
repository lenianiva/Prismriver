import Prismriver.Repr.Classical
import Lean.Elab

namespace Prismriver.Syntax

open Lean Prismriver.Classical

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
def accidentalFn : Parser.ParserFn :=
  Parser.nodeFn accidentalKind <|
  Parser.rawFn (trailingWs := true) fun ctx s =>
    let slice := ctx.substring s.pos ctx.endPos
    let slice' := slice.dropWhile (λ ch => markSharp.contains ch || markFlat.contains ch)
    if slice == slice' then
      s.mkErrorsAt [""] s.pos
    else
      s.setPos slice'.startPos
def accidentalNoAntiquot : Parser.Parser where
  fn := accidentalFn
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
def octaveFn : Parser.ParserFn :=
  Parser.nodeFn octaveKind <|
  Parser.rawFn (trailingWs := true) fun ctx s =>
    let slice := ctx.substring s.pos ctx.endPos
    let slice' := slice.dropWhile (λ ch => ch == markOctaveUp || ch == markOctaveDown)
    if slice == slice' then
      s.mkErrorsAt [""] s.pos
    else
      s.setPos slice'.startPos
def octaveNoAntiquot : Parser.Parser where
  fn := octaveFn
open PrettyPrinter Formatter in
@[combinator_formatter octaveNoAntiquot]
def octaveNoAntiquot.formatter : Formatter :=
  visitAtom octaveKind
open PrettyPrinter Parenthesizer in
@[combinator_parenthesizer octaveNoAntiquot]
def octaveNoAntiquot.parenthesizer : Parenthesizer := visitToken
def octave := Parser.withAntiquot (Parser.mkAntiquot "octave" octaveKind) octaveNoAntiquot

-- A music note is a pitch plus an optional duration
syntax hep optional(noWs accidental) optional(noWs octave) optional(num) : music_note

declare_syntax_cat music_seq
syntax music_note* : music_seq

def elabNote (stx : TSyntax `music_note) : Elab.Term.TermElabM Expr := do
  let `(music_note| $h:hep$[$acc?:accidental]?$[$oct?:octave]?$[$d:num]?) := stx
    | Elab.throwUnsupportedSyntax
  let h := (h.raw.isLit? hepKind).getD "c"
  let acc := acc?.bind (·.raw.isLit? accidentalKind) |>.getD ""
  let oct := oct?.bind (·.raw.isLit? octaveKind) |>.getD ""
  let d : Rat := mkRat 1 (d.map (·.getNat) |>.getD 4)
  let .some pitch := parsePitch h acc oct
    | Elab.throwUnsupportedSyntax
  let time : MeasuredTime := ⟨0, 0⟩
  let note ←
    Meta.withLocalInstances ((← getLCtx).decls.toList.filterMap (λ x => x)) do
    Meta.mkAppM ``Note.mk #[toExpr pitch, toExpr time, toExpr d]
  return note
  where
  parsePitch (p acc oct : String) : Option Pitch := do
    let hep ← match p with
      | "c" => pure Hep.c
      | "d" => pure Hep.d
      | "e" => pure Hep.e
      | "f" => pure Hep.f
      | "g" => pure Hep.g
      | "a" => pure Hep.a
      | "b" => pure Hep.b
      | _ => .none
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
    return Pitch.new hep oct ⟨acc⟩

syntax (name := music) "♩[" music_seq "]" : term

elab "♩[" seq:music_seq "]" : term <= type => do
  let `(music_seq| $notes:music_note* ) := seq
    | Elab.throwUnsupportedSyntax

  let .some noteType := type.app1? `List | Elab.throwUnsupportedSyntax

  let notes ← notes.mapM elabNote
  Meta.mkListLit noteType notes.toList

#eval (♩[ cs5 d e f ] : List (@Classical.Note time44))
#eval (♩[ c'' d e f5 ] : List (@Classical.Note time44))
#eval (♩[ c,,,, d e f5 ] : List (@Classical.Note time44))

def play (aldaCode : String) : IO UInt32 := do
  let lockFile := "/tmp/prismriver-alda.lock"
  let hLock ← IO.FS.Handle.mk lockFile .write
  let flag ← hLock.tryLock
  if !flag then
    return 0
  let ch ← IO.Process.spawn { cmd := "alda", args := #["play", "--code", aldaCode] }
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
  let code := s!"{notes}"

  logInfo s!"{code}"
  let ret ← play code
  if ret ≠ 0 then
    throwError s!"Subprocess failed: {ret}"

--#play ♩[e4 c'4 b4 d4 e2]
