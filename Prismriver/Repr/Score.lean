import Prismriver.Repr.Note
import Prismriver.Repr.Time
import Prismriver.Repr.Instrument

import Std.Data.TreeMap

namespace Prismriver

inductive ControlEvent
  /-- Indicate change of a bar -/
  | wall
  deriving Repr

instance : ToString ControlEvent where
  toString e := match e with
    | .wall => "|"

/-- An event occuring at some particular time -/
inductive Event (P T) [Time T] where
  -- Music note
  | note (n : Note P T) (instrument? : Option (Instrument P))
  -- Control behaviour event
  | control (e : ControlEvent)

instance [ToString P] [ToString T] [Time T] : ToString (Event P T) where
  toString event := match event with
    | .note n _instrument? => s!"{n}"
    | .control e => s!"{e}"

protected def Event.duration? { P T } [Time T] : Event P T → Option T
  | .note { duration, .. } _ => duration
  | .control .. => .none

/-- A music score -/
structure Score (P T) [Time T] where
  events : Std.TreeMap T (List (Event P T)) (cmp := Ord.compare) := .empty

variable { P T } [instTime : Time T]

instance [ToString P] [ToString T] : ToString (Score P T) where
  toString score := score.events.foldl (init := "") λ acc time events =>
    let events := events.foldl (init := "") λ acc e => s!"{acc} {e}"
    let line := s!"{time} [{events} ]"
    s!"{acc}\n{line}"

namespace Score

protected def addEvent (score : Score P T) (time : T) (event : Event P T)
  : Score P T :=
  let events' := score.events.insertIfNew time []
  let events'' := events'.modify time λ li => event :: li
  { score with events := events'' }

structure Context where
  time : T
  -- List of all active events at time `T`
  events : Std.TreeMap T (List (Event P T)) := .empty

/-- Returns new events generated in this instant -/
protected def Context.newEvents (context : @Context P T instTime) : List (Event P T) :=
  context.events.getD context.time []

/-- Chronological fold on a score. If `tail` is set to true, output a terminal instance with no events -/
protected def foldM [Monad M] [BEq T] (score : Score P T) (m : α → @Context P T instTime → M α) (init : α)
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
      let a' ← m a { time := maxT + instTime.bar }
      return a'
  return a

/-- Combine two scores-/
protected def merge (score1 score2 : Score P T) : Score P T :=
  {
    events := score1.events.mergeWith (λ _ es1 es2 => es1 ++ es2) score2.events
  }

end Score

/-- Score with notes being in et12 -/
abbrev EqualTemp.Score12 := @Prismriver.Score Int MeasuredTime
/-- Score with classical notes -/
abbrev Classical.Score := @Prismriver.Score Pitch MeasuredTime
