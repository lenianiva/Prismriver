import Prismriver.Repr.Note
import Prismriver.Repr.Instrument

namespace Prismriver

variable (P T D) [Time T D]

inductive ControlEvent
  /-- Indicate change of a bar -/
  | wall

/-- An event occuring at some particular time -/
inductive Event where
  -- Music note
  | note (n : Note P D) (instrument? : Option (Instrument P))
  -- Control behaviour event
  | control (e : ControlEvent)

/-- A music score -/
structure Score [Time T D] where
  events : List (T × List (Event P D))

namespace Score

def addEvent { P T D } [Time T D] (score : Score P T D) (event : Event P D) : Score P T D := sorry

structure Context where
  time : T
  events : List (Event P D)

/-- Chronological fold on a score -/
protected def foldM [Monad M] (score : Score P T D) (m : α → Context P T D → M α) (init : α)
: M α := do
  score.events.foldlM (init := init) λ acc (time, events) =>
    let context := { time, events }
    m acc context

end Score

/-- Score with notes being in et12 -/
abbrev EqualTemp.Score12 := @Prismriver.Score Int MeasuredTime Rat
/-- Score with classical notes -/
abbrev Classical.Score := @Prismriver.Score Pitch MeasuredTime Rat
