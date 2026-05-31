import Prismriver.Repr.Score

namespace Prismriver

namespace Composition

structure State (P T : Type) [time : Time T] where
  time : T := time.zero -- Current time
  score : Score P T := {}

/-- Monad for algorithmic composition -/
abbrev CompositionT (P T : Type) [Time T] := StateT (State P T)

variable { P T : Type } [Time T]

-- Monadic utilities about composition
section Monad

variable { M } [Monad M]

def addPart (partId : PartId) (part : Part) : CompositionT P T M Unit := do
  modify λ state => { state with score := { state.score with
    parts := state.score.parts.insert partId part
  }}

/-- Move the current time forward -/
def move [ShiftRight T] (d : T) : CompositionT P T M Unit := do
  modify λ state => { state with time := state.time >>> d }

/-- Insert a new event at the current time -/
def addEvent (event : Event P T)
  : CompositionT P T M Unit := do
  modify λ state => { state with score := state.score.addEvent state.time event }

/-- Insert a new note at the current time -/
def addNote [ShiftRight T] (note : Note P T) (partId? : Option PartId := .none) (still : Bool := false)
  : CompositionT P T M Unit := do
  addEvent $ Event.note note partId?
  if !still then
    move note.duration

end Monad

end Composition

export Composition (CompositionT)
abbrev Classical.CompositionT := @Composition.CompositionT Classical.Pitch MeasuredTime
