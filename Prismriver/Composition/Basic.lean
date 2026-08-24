import Prismriver.Repr.Score

namespace Prismriver

namespace Composition

structure State (P T : Type) [Time T] where
  time : T := Time.zero -- Current time
  score : Score P T := {}

class MonadComposition ( P T : outParam Type ) [Time T] (m : Type → Type) [Monad m] where
  currentTime : m T
  modify : (Score P T → Score P T) → m Unit

def currentTime { P T m } [instTime : Time T] [Monad m] [MonadComposition P T m] : m T := MonadComposition.currentTime

@[always_inline]
instance (P T m n) [Time T] [Monad m] [Monad n] [MonadLift m n] [MonadComposition P T m] : MonadComposition P T n where
  currentTime := liftM (MonadComposition.currentTime : m T)
  modify := fun f => liftM (MonadComposition.modify f : m Unit)

@[always_inline]
instance ( P T ) [Time T] [Monad m] [MonadState (State P T) m] : MonadComposition P T m where
  currentTime := do
    pure (← get).time
  modify f := liftM (modify λ state => { state with score := f state.score } : m Unit)

variable { P T : Type } [Time T]

-- Monadic utilities about composition
section Monad

variable { M } [Monad M] [MonadState (State P T) M] [MonadComposition P T M]

def addPart (partId : PartId) (part : Part) : M Unit := do
  modify λ state => { state with score := { state.score with
    parts := state.score.parts.insert partId part
  }}

/-- Move the current time forward -/
def move [ShiftRight T] (d : T) : M Unit := do
  modify λ state => { state with time := state.time >>> d }

/-- Insert a new event at the current time -/
def addEvent (event : Event P T) : M Unit := do
  modify λ state => { state with score := state.score.addEvent state.time event }

def getNewEvents : M (List (Event P T)) := do
  return (← get).score.newEventsAt (← currentTime)

/-- Insert a new note at the current time -/
def addNote [ShiftRight T] (note : Note P T) (partId? : Option PartId := .none) (still : Bool := false)
  : M Unit := do
  addEvent $ Event.note note partId?
  if !still then
    move note.duration

end Monad

/-- Simple monad for algorithmic composition -/
abbrev CompositionT (P T) [Time T] := StateT (State P T)

def compose { P T } [Time T] { M } [Monad M] (m : CompositionT P T M Unit) : M (Score P T) := do
  let ((), { score, .. }) ← m.run {}
  return score

/-- Side-effect free compose -/
def compose' { P T } [Time T] (m : CompositionT P T Id Unit) : Score P T := compose (Id.run m)

instance [ShiftRight T] : Coe (List (Note P T)) (Score P T) where
  coe li := compose <| Id.run <| show CompositionT P T Id Unit from do
    for note in li do
      addNote note

end Composition

export Composition (CompositionT)
abbrev Classical.CompositionT := @Composition.CompositionT Classical.Pitch MeasuredTime
