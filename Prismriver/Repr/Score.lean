import Prismriver.Repr.Note
import Prismriver.Repr.Instrument

namespace Prismriver

variable { P I T D } [HAdd P I P]

inductive ControlEvent
  | scaleChange (scale : Scale P I)

/-- An event occuring at some particular time -/
inductive Event where
  -- Music note
  | note (n : Note P Rat) (instrument? : Option (Instrument P I))
  -- Control behaviour event
  | control (e : @ControlEvent P I _)

/-- A music score -/
structure Score [Time T D] where
  events : List (T × List (@Event P I _))

namespace Score

variable [Time T D]

structure Context where
  time : T
  events : List (@Event P I _)

/-- Chronological fold on a score -/
protected def foldM [Monad M] (m : α → @Context P I T _ → M α) (init : α) (score : @Score P I T D _ _)
: M α := do
  score.events.foldlM (init := init) λ acc (time, events) =>
    let context := { time, events }
    m acc context

end Score

abbrev Classical.Score := @Prismriver.Score Pitch Classical.Interval MeasuredTime Rat
