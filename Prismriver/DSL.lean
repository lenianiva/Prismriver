import Prismriver.Repr.Classical
import Lean.Elab

namespace Prismriver

open Lean Prismriver.Classical

declare_syntax_cat music
syntax (name := note) ident : music
syntax "{" music* "}" : music

syntax (name := music) "♩[" music "]" : term

@[macro music] def musicUnfold : Macro
  | `(music|d) => `(term|c)
  | `(music|$x:ident) => `(term|$x)
  | `(music|{ $x:music* }) => do
    let x ← x.mapM λ y => `(♩[$y])
    `(term|[$x,*])
  | _ => Macro.throwUnsupported

partial def elabMusic (stx : TSyntax `music) : Elab.Term.TermElabM Expr := do
  logInfo s!"{stx}"
  match stx with
  | `(music|$key:ident) => do
    let s := key.getId
    let [comp] := s.components | Elab.throwUnsupportedSyntax
    let chs := comp.toString
    let hep ← match chs.front with
      | 'c' => pure Hep.c
      | 'd' => pure Hep.d
      | 'e' => pure Hep.e
      | 'f' => pure Hep.f
      | 'g' => pure Hep.g
      | 'a' => pure Hep.a
      | 'b' => pure Hep.b
      | _ => Elab.throwUnsupportedSyntax
    pure (.lit (.natVal hep.toNat))
  | `(music|{ $xs:music* }) =>
    let notes ← xs.mapM elabMusic
    let nat ← Meta.mkConstWithFreshMVarLevels `Nat
    Meta.mkListLit nat notes.toList
  | _ => Elab.throwUnsupportedSyntax

@[term_elab music]
def musicImpl : Elab.Term.TermElab := λ stx _type? => do
  match stx with
  | `(♩[$z:music]) =>
    elabMusic z
  | _ => Elab.throwUnsupportedSyntax

#eval ♩[ { c d e f5 }]
