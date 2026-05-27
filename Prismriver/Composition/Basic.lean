import Prismriver.Repr.Score

namespace Prismriver

namespace Composition

variable (P T D : Type) [Time T D]

structure State where
  time : T -- Current time
  score : Score P T D

/-- Monad for algorithmic composition -/
abbrev CompositionT := StateT (State P T D)

section Monad

variable { M } [Monad M]

/-- Move the current time forward -/
def move (d : D) : CompositionT P T D M Unit := do
  modify λ state => { state with time := state.time + d }

def addNote (note : Note P D) (instrument? : Option (Instrument P) := .none)
  : CompositionT P T D M Unit := do
  let event := Event.note note instrument?
  modify λ state => { state with score := state.score.addEvent event }

end Monad

end Composition

export Composition (CompositionT)
