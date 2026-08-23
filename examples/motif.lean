import Prismriver.Composition.ChordProgression
import Prismriver.Composition.Motif
import Prismriver.IO.MusicXML

open Prismriver Classical Composition

structure Context where
  --scale : Scale Pitch Interval := diatonic ⟨.d, .natural⟩ .d
  scale : Scale Pitch Interval := japanese_in ⟨.d, .natural⟩

/-- Ending motif -/
def motif0 := Motif.arpeggio (rt 1 2) [true, false]
/-- Baseline motif -/
def motif1 := Motif.arpeggio (rt 1 4) [true, false, true, false]
def motif2 := 2 • (Motif.constant (rt 1 4 |>.dot) false) ++ (Motif.constant (rt 1 4 |>.dot) true)

def motifSmall1 := Motif.multi [(rt 1 8, Interval.unison), (rt 1 16, -.mi2), (rt 1 16, .unison)]

def randPieceM : ReaderT Context (Classical.CompositionT (RandomT IO)) Unit := do
  let length := 9
  let context ← read
  let tonic := (4 * context.scale.fundamental) • context.scale.pitches[0]!
  let baseChord := tonic :: minor3.map (· • tonic)
  -- generate random chord
  let chords := (← randChordProgression context.scale length) ++ [baseChord]
  let baseMotifs := #[motif0, motif1, motif2]

  -- generate music
  addPart 0 { instrument? := .some Instrument.acoustic_grand }
  addEvent $ .control (.key (diatonicFifths ⟨.d, .natural⟩ .d))

  for chord in chords do
    -- Generate 1 bar with this chord
    IO.eprintln s!"chord: {chord}"

    let motif ← genChoice #[1, 1, 1] baseMotifs
    let motif := motif.mapValues λ flag => if flag then chord[0]! else chord[1]!
    let motif := if ← genBool (mkRat 1 3) then
        motif.replace motifSmall1 (λ p i => i • p)
      else
        motif

    -- create the notes
    let notes := motif.intersect λ p => [p]
    for (_, note) in notes do
      addPianoNote note

    -- sample from chords
    move .bar
  addPianoNote ⟨tonic, mkRat 1 1⟩
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

`lake env lean --run examples/motif.lean | alda import -i musicxml | alda play`
-/
def main : IO UInt32 := do
  let score ← randPiece
  IO.eprintln s!"{score}"
  let xml := score.toMusicXML
  IO.println s!"{xml}"
  return 0
