import Prismriver.Composition.ChordProgression
import Prismriver.Composition.Motif
import Prismriver.IO.MusicXML
import Prismriver.Repr.Classical

open Prismriver Classical Composition

variable [Time T]

structure TimeSignature where
  top : Nat
  bottom : Nat
  deriving Ord, BEq

structure Context where
  scale : Scale Pitch Interval := diatonic ⟨.d, .natural⟩ .d
 -- scale : Scale Pitch Interval := japanese_in ⟨.d, .natural⟩
  -- on chord notes will tend to fall on strong beats
  -- Baseline sampling weight.
  timeSignature : TimeSignature
  baselineWeight : Nat := 1

def randMotif (context : Context) (duration: T) (notes := context.scale.pitches.length ) : RandomT IO (@MotifTime T _) := do
   return match ← genRange 0 2 with
   | 0 => constantMotif duration notes
   | 1 => apregMotif duration notes
   | _ => constantMotif duration notes

def randPieceM : ReaderT Context (Classical.CompositionT (RandomT IO)) Unit := do
  let length := 9
  let context ← read
  let basePitch := (4 * context.scale.fundamental) • context.scale.pitches[0]!
  -- generate random chord

  let chords := (← randChordProgression context.scale length)
  let duration := (mkRat 1 context.timeSignature.bottom : MeasuredTime)
  let motifs := [← randMotif context duration, ← randMotif context duration, ← randMotif context duration]
  -- generate music
  addPart 0 { instrument? := .some Instrument.violin }
--  addEvent $ .control (.fifth (diatonicFifths ⟨.d, .natural⟩ .d))

  for chord in chords do
    IO.eprintln s!"chord: {chord}"
--    let motif ← genChoice #[1, 1, 1] motifs
    let profile : Array (_ × Nat) := createSampleProfileAtChord chord 1
    let pitchIdx ← genWeighted (profile.map (·.2))
    -- Create sampling profile for pitch
    let p0 := profile[pitchIdx]!.1
--    motifs.foldl (init := [])

    for motif in motifs do
--      let step := motif.division.times[i+1]! - motif.division.times[i]!
 --     let interval := motif.intervals[i]!
      -- Create sampling profile for pitch
      let intersection := intersect motif chords
      for pair in intersection do
        for note in chord do
          addPianoNote ⟨ ⟨ note.name, note.acc ⟩  , pair.snd.duration⟩

    move .bar
  where
  addPianoNote (note: Classical.Note) := addNote note (partId? := .some 0)
  createSampleProfileAtChord (ch : Chord) (_beatStrength : Nat)
    := ch.toArray.zip #[1, 1, 1]

def randPiece : IO Classical.Score := do
  let context : Context := {timeSignature := {top := 4, bottom := 4}}
  let result ← (compose $ randPieceM.run context).run' (mkStdGen)
  return result

-- lake env lean --run examples/motif-test.lean | alda import -i musicxml | alda play

def main : IO UInt32 := do
  let score ← randPiece
  IO.eprintln s!"{score}"
  let xml := score.toMusicXML
  IO.println s!"{xml}"
  return 0
