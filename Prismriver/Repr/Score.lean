import Prismriver.Repr.Note
import Prismriver.Repr.Instrument

namespace Prismriver

variable (P T D)

inductive ControlEvent
  | scaleChange (scale : Scale P)

/-- An event occuring at some particular time -/
inductive Event where
  -- Music note
  | note (n : Note P Rat) (instrument? : Option (Instrument P))
  -- Control behaviour event
  | control (e : ControlEvent P)

/-- A music score -/
structure Score [Time T D] where
  events : List (T × List (Event P))

namespace Score

variable [Time T D]

structure Context where
  time : T
  events : List (Event P)

/-- Chronological fold on a score -/
protected def foldM [Monad M] (score : Score P T D) (m : α → Context P T → M α) (init : α)
: M α := do
  score.events.foldlM (init := init) λ acc (time, events) =>
    let context := { time, events }
    m acc context

end Score

abbrev Classical.Score := @Prismriver.Score Pitch MeasuredTime Rat
