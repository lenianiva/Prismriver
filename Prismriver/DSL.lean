import Prismriver.Repr.Classical
import Lean.Elab

namespace Prismriver

open Lean Prismriver.Classical

declare_syntax_cat mystery
syntax (name := mystery1) ident ","* : mystery

declare_syntax_cat music
syntax (name := note) ident : music
syntax (name := note1) ident ","* optional(num) : music
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

def parseNote (z : Ident) (octaveDown : Nat := 0) (duration : Nat := 0)
  : Elab.Term.TermElabM Expr := do
  let id := z.getId
  let (pitch, octaveUp, duration') := divideNote id.toString
  let duration := duration + (duration'.toNat?.getD 0)
  --let duration := chs.drop 1 |>.dropRightWhile (!·.isDigit) |>.toNat?.getD 4
  let .some (hep, acc) := parsePitch pitch
    | Elab.throwUnsupportedSyntax
  let octaveUp : Except Nat Nat := octaveUp.foldr (init := .ok 0) λ ch acc =>
    match (acc, ch) with
    | (.ok n , '\'') => .ok (n + 1)
    | (.ok n, _) => .error n
    | (e, _) => e
  let octaveUp := match octaveUp with
    | .ok n => n
    | .error n => n
  let octave := (octaveUp : Int) - (octaveDown : Int)
  let pitch := Pitch.new hep octave acc
  return Lean.toExpr pitch
  where
  /-- Divide note into pitch, octaveUp, duration markers -/
  divideNote (n : String) : (Substring × Substring × Substring) :=
    let i := n.find (· = '\'')
    let j := n.find (·.isDigit)
    let pitch := Substring.mk n ⟨0⟩ (i.min j)
    let octaveUp := Substring.mk n i j
    let duration := Substring.mk n j n.endPos
    (pitch, octaveUp, duration)
  parsePitch (p : Substring) : Option (Hep × Accidental) := do
    let hep ← match p.front with
      | 'c' => pure Hep.c
      | 'd' => pure Hep.d
      | 'e' => pure Hep.e
      | 'f' => pure Hep.f
      | 'g' => pure Hep.g
      | 'a' => pure Hep.a
      | 'b' => pure Hep.b
      | _ => .none
    let acc ← parseAcc (p.drop 1)
    return (hep, acc)
  parseAcc (a : Substring) : Option Accidental := do
    let n ← match a.take 1 |>.toString with
      -- HACK: Not checking if the accidentals are all sharps or flats
      | "s" => pure (a.bsize : Int)
      | "f" => pure (-a.bsize : Int)
      | "" => pure 0
      | _ => .none
    return ⟨n⟩

partial def elabMusic (type : Expr) (stx : TSyntax `music) : Elab.Term.TermElabM Expr := do
  match stx with
  | `(music|$key:ident) => do
    parseNote key
  | `(music|$key:ident $[,%$occ]* $(o?)?) => do
    let duration := o?.map (·.getNat) |>.getD 0
    parseNote key (octaveDown := occ.size) (duration := duration)
  | `(music|{ $xs:music* }) =>
    let notes ← xs.mapM (elabMusic type)
    --let t := Lean.toTypeExpr (@Classical.Note (S := timeSignature 4 4))
    Meta.mkListLit type notes.toList
  | _ =>
    Elab.throwUnsupportedSyntax

@[term_elab music]
def musicImpl : Elab.Term.TermElab := λ stx type? => do
  let .some type := type? | Elab.throwPostpone
  let .some type := type.app1? `List | Elab.throwUnsupportedSyntax
  match stx with
  | `(♩[$z:music]) =>
    elabMusic type z
  | _ =>
    Elab.throwUnsupportedSyntax

#eval (♩[ { c5 d e f }] : List Pitch)
#eval (♩[ { c'' d e f5 }] : List Pitch)
#eval (♩[ { c,,,, d e f5 }] : List Pitch)
