import Lean.Elab

open Lean

namespace Prismriver

declare_syntax_cat music
syntax (name := note) ident : music
syntax note,* : music

syntax (name := music) "♩[" music "]" : term

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
