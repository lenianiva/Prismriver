import Prismriver.Repr.Classical
import Lean.Elab

namespace Prismriver

open Lean Prismriver.Classical

declare_syntax_cat mystery
syntax (name := mystery1) ident ","* : mystery

declare_syntax_cat music
syntax (name := note) ident : music
syntax (name := note1) ident ","* : music
syntax "{" music* "}" : music

syntax (name := music) "♩[" music "]" : term

@[macro music] def musicUnfold : Macro
  | `(music|d) => `(term|c)
  | `(music|$x:ident $[,%$occ]*) => do
    `(term|$x)
  | `(music|{ $x:music* }) => do
    let x ← x.mapM λ y => `(♩[$y])
    `(term|[$x,*])
  | _ => Macro.throwUnsupported

def parseNote (z : Ident) (sharps : Nat := 0) : Elab.Term.TermElabM Expr := do
  let id := z.getId
  let chs := id.toString
  let hep ← match chs.front with
    | 'c' => pure Hep.c
    | 'd' => pure Hep.d
    | 'e' => pure Hep.e
    | 'f' => pure Hep.f
    | 'g' => pure Hep.g
    | 'a' => pure Hep.a
    | 'b' => pure Hep.b
    | _ => Elab.throwUnsupportedSyntax
  let octave := chs.drop 1 |>.dropRightWhile (!·.isDigit) |>.toNat?.getD 0
  let flats : Except Nat Nat := chs.drop 1 |>.foldr (init := .ok 0) λ ch acc =>
    match (acc, ch) with
    | (.ok n , '\'') => .ok (n + 1)
    | (.ok n, _) => .error n
    | (e, _) => e
  let flats := match flats with
    | .ok n => n
    | .error n => n
  let acc := ⟨(sharps : Int) - (flats : Int)⟩
  let pitch := Pitch.new hep octave acc
  return Lean.toExpr pitch

partial def elabMusic (stx : TSyntax `music) : Elab.Term.TermElabM Expr := do
  logInfo s!"{stx}"
  match stx with
  | `(music|$key:ident) => do
    parseNote key
  | `(music|$key:ident $[,%$occ]*) => do
    parseNote key (sharps := occ.size)
  | `(music|{ $xs:music* }) =>
    let notes ← xs.mapM elabMusic
    let t := Lean.toTypeExpr Pitch
    Meta.mkListLit t notes.toList
  | _ => Elab.throwUnsupportedSyntax

@[term_elab music]
def musicImpl : Elab.Term.TermElab := λ stx _type? => do
  match stx with
  | `(♩[$z:music]) =>
    elabMusic z
  | _ => Elab.throwUnsupportedSyntax

#eval ♩[ { c'' d e f5 }]
#eval ♩[ { c,,,, d e f5 }]
