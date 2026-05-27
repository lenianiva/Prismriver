import Prismriver.Repr.Note
import Prismriver.Repr.Instrument

namespace Prismriver

variable (P I T D)

inductive ControlEvent
  | scaleChange (scale : Scale P I)
  /-- Indicate change of a bar -/
  | wall

/-- An event occuring at some particular time -/
inductive Event where
  -- Music note
  | note (n : Note P Rat) (instrument? : Option (Instrument P I))
  -- Control behaviour event
  | control (e : ControlEvent P I)

/-- A music score -/
structure Score [Time T D] where
  events : List (T × List (Event P I))

namespace Score

variable [Time T D]

structure Context where
  time : T
  events : List (Event P I)

/-- Chronological fold on a score -/
protected def foldM [Monad M] (score : Score P I T D) (m : α → Context P I T → M α) (init : α)
: M α := do
  score.events.foldlM (init := init) λ acc (time, events) =>
    let context := { time, events }
    m acc context

end Score

abbrev Classical.Score := @Prismriver.Score Pitch Classical.Interval MeasuredTime Rat
