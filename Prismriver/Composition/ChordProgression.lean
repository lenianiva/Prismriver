import Prismriver.Composition.Basic
import Prismriver.Composition.Random
import Prismriver.Repr.Classical

namespace Prismriver.Composition

open Classical

abbrev Chord := List Pitch

section Generators

variable { g } [RandomGen g]
variable { m } [Monad m] [MonadRandom g m]

/-- create random pitch from scale -/
def randPitch (scale : Scale Pitch Interval) : m Pitch := do
  let i ← genRange 0 scale.pitches.length
  return scale.pitches[i]!

def invertChord1 (p : List Pitch) : Chord :=
  let f := Interval.octave
  [(-f) • p[2]!, p[0]!, p[1]!]
def invertChord2 (p : List Pitch) : Chord :=
  let f := Interval.octave
  [(-f) • p[1]!, (-f) • p[2]!, p[0]!]

/-- Create a random chord -/
def randChord (pitch : Pitch) : m Chord := do
  let base := match ← genRange 0 1 with
    | 0 => pitch :: major3.map (· • pitch)
    | _ => pitch :: minor3.map (· • pitch)
  return match ← genRange 0 2 with
    | 0 => base
    | 1 => invertChord1 base
    | _ => invertChord2 base

/-- Generate a random chord progression -/
def randChordProgression (scale : Scale Pitch Interval) (n : Nat) : m (List Chord) := do
  List.range n |>.mapM λ _i => do
    let p := (4 * scale.fundamental) • (← randPitch scale)
    let ch ← randChord p
    pure ch

def randStep (minDiv : Nat := 1) (maxDiv : Nat := 3) : m Rat := do
  let z ← genRange minDiv maxDiv
  let den := 1 <<< z
  return mkRat 1 den

end Generators
