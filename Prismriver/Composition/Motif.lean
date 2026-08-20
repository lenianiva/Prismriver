import Prismriver.Repr.Note
import Prismriver.Repr.Time
namespace Prismriver.Composition

variable [Time T]

structure TimeMeasuredTime where
  time : T
  duration : T
  deriving Ord, BEq

structure MotifTime where
  components : Std.TreeMap (@TimeMeasuredTime T) (List Nat)
  deriving Inhabited

def intersect [Inhabited P] (motif : @MotifTime T _) (chords : List P) : List (T × Note P T) :=
  motif.components.foldl (init := []) λ acc p v =>
    let newNotes := v.map λ i =>
      (
        p.time,
        ({ duration := p.duration, pitch := chords[i]! } : Note P T),
      )
    acc ++ newNotes

-- (time, duration) -> [Nat]
-- (1/4, 1/4) -> [2, 3]
-- when this motif meets the C major chord C/E/G, we get
-- (1/4 E, 1/4 G)

-- random motif time
-- most simple motif - hit every note in the chord; given the duration (ex 1 measure) and 3 notes in a chord, we generate motif that hits all 3 as a chord
-- arpeggio - hit notes in a sequence
-- long long short, long long short

-- for each component in MotifTime
-- sample a motif
-- combine the random motif with the intersection of chord progresions and motif time

def simpleMotif (timeNotePair: T × Note P T) (chords : List P) : List (T × Note P T) :=
  chords.foldl (init := []) λ acc chord =>
    acc ++ (
        timeNotePair.fst,

      )
  acc
