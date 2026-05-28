import Prismriver.Repr.Note
import Prismriver.Repr.Time
import Prismriver.Repr.Instrument

import Std.Data.TreeMap

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

protected def Event.duration? : Event P D → Option D
  | .note { duration, .. } _ => duration
  | .control .. => .none

/-- A music score -/
structure Score [Time T D] where
  events : Std.TreeMap T (List (Event P D)) (cmp := Ord.compare) := .empty

namespace Score

protected def addEvent { P T D } [Time T D] (score : Score P T D) (time : T) (event : Event P D)
  : Score P T D :=
  let events' := score.events.insertIfNew time []
  let events'' := events'.modify time λ li => event :: li
  { score with events := events'' }

structure Context where
  time : T
  -- List of all active events at time `T`
  events : Std.TreeMap T (List (Event P D)) := .empty

/-- Returns new events generated in this instant -/
protected def Context.newEvents (context : Context P T D) : List (Event P D) :=
  context.events.getD context.time []

/-- Chronological fold on a score. If `tail` is set to true, output a terminal instance with no events -/
protected def foldM [Monad M] [BEq T] (score : Score P T D) (m : α → Context P T D → M α) (init : α)
  (tail : Bool := true)
  : M α := do
  let (a, es) ← score.events.foldlM (init := (init, Std.TreeMap.empty))
    λ (acc, lingering) time events => do
      let lingering := lingering.filterMap λ t es =>
        let es := es.filter λ e =>
          -- HACK: Use `<`?
          e.duration?.map (λ d => compare time (t + d) == Ordering.lt) |>.getD false
        if es.isEmpty then .none else .some es
      let context := { time, events := lingering.insert time events }
      let a ← m acc context
      pure (a, context.events)
  if tail then if let .some t0 := es.minKey? then
    -- Generate one last time slice
    let maxT := es.foldl (init := t0) λ maxT time events =>
      let maxET? := events.filterMap (·.duration?.map (time + ·)) |>.max?
      match maxET? with
      | .some t' => max maxT t'
      | .none => maxT
    if maxT != t0 then
      -- Create one last temporal instance
      let a' ← m a { time := maxT }
      return a'
  return a

/-- Combine two scores-/
protected def merge (score1 score2 : Score P T D) : Score P T D :=
  {
    events := score1.events.mergeWith (λ _ es1 es2 => es1 ++ es2) score2.events
  }

end Score

/-- Score with notes being in et12 -/
abbrev EqualTemp.Score12 := @Prismriver.Score Int MeasuredTime Rat
/-- Score with classical notes -/
abbrev Classical.Score := @Prismriver.Score Pitch MeasuredTime Rat
