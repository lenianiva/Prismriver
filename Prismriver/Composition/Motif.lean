import Prismriver.Repr.Note
import Prismriver.Repr.Time
namespace Prismriver.Composition

variable [Time T]

/-- Mapping of time spans to a list of objects -/
structure Motif (V) where
  components : Std.TreeMap (@TimeSpan T _) V := .empty
  deriving Inhabited, BEq

/-- Repeat the second motif along every note in the first motif -/
instance { α β } : HShiftRight (@Motif T _ α) (@Motif T _ β) (@Motif T _ (α × β)) where
  hShiftRight m1 m2 :=
    {
      components := m1.components.foldl (init := .empty) λ acc k a =>
        m2.components.foldl (init := acc) λ acc' k' b =>
          let span := { start := k.start + k'.start, duration := k'.duration }
          acc'.insert span (a, b)
    }

/-- Scale the time dimension by a scalar -/
instance [SMul S T] { V } : SMul S (@Motif T _ V) where
  smul s m :=
    { components := m.components.foldl (init := .empty) λ acc t notes =>
        acc.insert ⟨s • t.start, s • t.duration⟩ notes }

namespace Motif

/-- Map an indeterminant motif with a function that produces notes -/
protected def intersect { α β } (motif : @Motif T _ α) (f : α → List β) : List (T × Note β T) :=
  motif.components.foldl (init := []) λ acc p a =>
    let newNotes := (f a).map λ pitch =>
      (
        p.start,
        { duration := p.duration, pitch },
      )
    acc ++ newNotes

protected def render [Torsor P I] (motif : @Motif T _ (List I)) (base : P) : List (T × Note P T) :=
  motif.intersect λ intervals => intervals.map (· • base)

/-- Intersect a motif from a list of pitches -/
protected def intersectList [Inhabited P] (motif : @Motif T _ (List Nat)) (pitches : List P) : List (T × Note P T) :=
  motif.intersect λ is => is.map (pitches[·]!)

variable { α }

/-- Map the values in a motif -/
protected def mapValues { β } (motif : @Motif T _ α) (f : α → β) : @Motif T _ β :=
  {
    components := motif.components.map λ _ => f
  }

/-- Total duration of a motif -/
protected def duration (motif : @Motif T _ α) : T :=
  motif.components.foldl (init := Time.zero) λ acc timespan _ =>
    max acc timespan.stop

-- (time, duration) -> [Nat]
-- (1/4, 1/4) -> [2, 3]
-- when this motif meets the C major chord C/E/G, we get
-- (1/4 E, 1/4 G)

-- for each component in Motif
-- sample a motif
-- combine the random motif with the intersection of chord progresions and motif time
-- take # of notes in chord

-- Generates a motif for a constant
def constant (duration : T) (a : α) : @Motif T _ α :=
  let components := Std.TreeMap.empty.insert ⟨Time.zero, duration⟩ a
  { components }

-- Arpeggiation on a list
def arpeggio (duration : T) (entries : List α) : @Motif T _ α :=
  let (_, components) := entries.foldl (init := (Time.zero, Std.TreeMap.empty)) λ (time, acc) a =>
    ((time + duration), acc.insert ⟨time, duration⟩ a)
  { components }

end Motif
