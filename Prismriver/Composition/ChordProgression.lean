import Prismriver.Composition.Basic
import Prismriver.Composition.Random
import Prismriver.Repr.Classical

namespace Prismriver.Composition

open Classical

abbrev Chord := List Pitch

structure Context where
  scale : Scale Pitch Interval := diatonic ⟨.d, .natural⟩ .d
  -- on chord notes will tend to fall on strong beats
  -- Baseline sampling weight
  baselineWeight : Nat := 1

protected def Context.beatStrengthAt (_c : Context) (t : Rat) : Nat :=
  match t with
  | Rat.mk' 0 1 _ _ => 4
  | Rat.mk' 1 2 _ _ => 2
  | _ => 1

section Generators

variable { g } [RandomGen g]
variable { m } [Monad m] [MonadRandom g m]

/-- create random pitch from scale -/
def randPitch (scale : Scale Pitch Interval) : m Pitch := do
  let i ← genRange 0 scale.pitches.length
  return scale.pitches[i]!

/-- Create a random chord -/
def randChord (scale : Scale Pitch Interval) (pitch : Pitch) : m Chord := do
  let base := match ← genRange 0 1 with
    | 0 => majorTriad pitch
    | _ => minorTriad pitch
  let i1 := scale.fundamental
  return match ← genRange 0 2 with
    | 0 => base
    | 1 => [(-i1) • base[2]!, base[0]!, base[1]!]
    | _ => [(-i1) • base[1]!, (-i1) • base[2]!, base[0]!]

/-- Generate a random chord progression -/
def randChordProgression (scale : Scale Pitch Interval) (n : Nat) : m (List Chord) := do
  List.range n |>.mapM λ _i => do
    let p := (4 * scale.fundamental) • (← randPitch scale)
    let ch ← randChord scale p
    pure ch

def randStep (minDiv : Nat := 1) (maxDiv : Nat := 4) : m Rat := do
  let z ← genRange minDiv maxDiv
  let den := 1 <<< z
  return mkRat 1 den

end Generators

def randPieceM : ReaderT Context (Classical.CompositionT (RandomT IO)) Unit := do
  let length := 5
  let context ← read
  let basePitch := (4 * context.scale.fundamental) • context.scale.pitches[0]!
  -- generate random chord
  let chords := (← randChordProgression context.scale length) ++ [minorTriad basePitch]

  -- generate music
  addPart 0 { instrument? := .some Instrument.acoustic_grand }

  for chord in chords do
    IO.eprintln s!"chord: {chord}"
    repeat
      let t : MeasuredTime ← currentTime
      if t.offset >= mkRat 1 1 then
        break

      let wBeatStrength := context.beatStrengthAt t.offset
      let step ← randStep
      let profile : Array (_ × Nat) := createSampleProfileAtChord chord wBeatStrength
      let pitchIdx ← genWeighted (profile.map (·.2))
      -- Create sampling profile for pitch
      let pitch := profile[pitchIdx]!.1
      addPianoNote ⟨pitch, step⟩

    -- sample from chords
    move .bar
  addPianoNote ⟨basePitch, mkRat 1 1⟩
  where
  addPianoNote (note: Classical.Note) := addNote note (partId? := .some 0)
  createSampleProfileAtChord (ch : Chord) (beatStrength : Nat)
    := ch.toArray.zip #[1, 1, 1]

def randPiece : IO Classical.Score := do
  let context : Context := {}
  let result ← (compose $ randPieceM.run context).run' (mkStdGen)
  return result
