import Lean.Elab

open Lean

namespace Prismriver

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

def elabNote (stx : TSyntax `music) : Elab.Term.TermElabM Expr := do
  logInfo s!"{stx}"
  match stx with
  | `(music|c) => pure (.lit (.natVal 2))
  | `(music|d) => pure (.lit (.natVal 3))
  | _ => Elab.throwUnsupportedSyntax

@[term_elab music]
def musicImpl : Elab.Term.TermElab := λ stx _type? => do
  match stx with
  | `(♩[$z:music]) =>
    elabNote z
  | _ => Elab.throwUnsupportedSyntax

#eval ♩[ c ]
