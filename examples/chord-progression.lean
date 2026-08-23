-- Random chord progression
import Prismriver.Composition.ChordProgression
import Prismriver.IO.MusicXML

open Prismriver Classical Composition

structure Context where
  --scale : Scale Pitch Interval := diatonic ⟨.d, .natural⟩ .d
  scale : Scale Pitch Interval := japanese_in ⟨.d, .natural⟩
  -- on chord notes will tend to fall on strong beats
  -- Baseline sampling weight
  baselineWeight : Nat := 1

protected def Context.beatStrengthAt (_c : Context) (t : Rat) : Nat :=
  match t with
  | Rat.mk' 0 1 _ _ => 4
  | Rat.mk' 1 2 _ _ => 2
  | _ => 1

def randDivision : RandomT IO Division := do
  let mut t : MeasuredTime := Time.zero
  let mut lines := [t]
  repeat
    if t.offset >= mkRat 1 1 then
      break
    let d ← randStep (maxDiv := 3)
    t := t + d
    lines := lines ++ [t]
  lines := lines ++ [(mkRat 1 1 : MeasuredTime)]
  return Division.fromLines lines

structure Motif where
  division : Division
  intervals : List Interval
  deriving Inhabited

protected def Motif.length (m : Motif) : Nat := m.division.times.length - 1

def randMotif (context : Context) : RandomT IO Motif := do
  let division ← randDivision
  let p0 := context.scale.pitches[0]!
  let chord := minorTriad p0
  let intervals ← division.times.mapM λ t => do
    let wBeatStrength := context.beatStrengthAt t.offset
    let profile : Array (_ × Nat) := createSampleProfileAtChord chord wBeatStrength
    let pitchIdx ← genWeighted (profile.map (·.2))
    -- Create sampling profile for pitch
    let pitch := profile[pitchIdx]!.1
    return pitch / p0
  return { division, intervals }
  where
  createSampleProfileAtChord (ch : Chord) (_beatStrength : Nat)
    := ch.toArray.zip #[1, 1, 1]

def randPieceM : ReaderT Context (Classical.CompositionT (RandomT IO)) Unit := do
  let length := 9
  let context ← read
  let basePitch := (4 * context.scale.fundamental) • context.scale.pitches[0]!
  -- generate random chord
  let chords := (← randChordProgression context.scale length) ++ [minorTriad basePitch]
  let motifs := #[← randMotif context, ← randMotif context, ← randMotif context]

  -- generate music
  addPart 0 { instrument? := .some Instrument.acoustic_grand }
  addEvent $ .control (.fifth (diatonicFifths ⟨.d, .natural⟩ .d))

  for chord in chords do
    IO.eprintln s!"chord: {chord}"
    let motif ← genChoice #[1, 1, 1] motifs
    let profile : Array (_ × Nat) := createSampleProfileAtChord chord 1
    let pitchIdx ← genWeighted (profile.map (·.2))
    -- Create sampling profile for pitch
    let p0 := profile[pitchIdx]!.1
    for i in List.range motif.length do
      let step := motif.division.times[i+1]! - motif.division.times[i]!
      let interval := motif.intervals[i]!
      -- Create sampling profile for pitch
      let pitch := interval • p0
      addPianoNote ⟨pitch, step⟩

    -- sample from chords
    move .bar
  addPianoNote ⟨basePitch, mkRat 1 1⟩
  where
  addPianoNote (note: Classical.Note) := addNote note (partId? := .some 0)
  createSampleProfileAtChord (ch : Chord) (_beatStrength : Nat)
    := ch.toArray.zip #[1, 1, 1]

def randPiece : IO Classical.Score := do
  let context : Context := {}
  let result ← (compose $ randPieceM.run context).run' (mkStdGen)
  return result
/--
Usage:

`lake env lean --run examples/chord-progression.lean | alda import -i musicxml | alda play`
-/
def main : IO UInt32 := do
  let score ← randPiece
  IO.eprintln s!"{score}"
  let xml := score.toMusicXML
  IO.println s!"{xml}"
  return 0
