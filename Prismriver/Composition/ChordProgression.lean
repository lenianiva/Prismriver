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

/-- Create a random chord -/
def randChord (pitch : Pitch) : m Chord := do
  return match ← genRange 0 1 with
  | 0 => majorTriad pitch
  | _ => minorTriad pitch

/-- Generate a random chord progression -/
def randChordProgression (scale : Scale Pitch Interval) (n : Nat) : m (List Chord) := do
  List.range n |>.mapM λ _i => do
    let p ← randPitch scale
    let ch ← randChord p
    pure ch

end Generators
