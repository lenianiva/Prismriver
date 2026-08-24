import Prismriver.Example.Touhou
import Prismriver.Composition.Motif
import Prismriver.IO.MusicXML

open Prismriver Prismriver.Classical Prismriver.Composition

def addPianoNote (note: Classical.Note)
  : Classical.CompositionT Id Unit := addNote note (partId? := .some 0) --(still := true)

/-- Ending motif -/
def motif0 := Motif.arpeggio (rt 1 2) [true, false]
/-- Baseline motif -/
def motif1 := Motif.arpeggio (rt 1 4) [0, 0, 1, 2]
def motif2 := Motif.arpeggio (rt 1 8) [0, 1, 0, 2, 0, 1, 0, 2]

def generateAccompaniment : Classical.CompositionT Id Unit := do
  --let mut bar := 0
  let motif := motif1
  addPart 1 { instrument? := .some Instrument.acoustic_grand }
  return ()
  repeat do
    let chord := (← getNewEvents).filterMap λ
      | .note { pitch := p, .. } .none => .some p
      | _ => .none
    let _base :: _rest := chord | break
    let notes := motif.intersect λ i => [chord[i]!]
    for (_, note) in notes do
      addPianoNote note
      --move duration

    --move base.duration
    move .bar

/--
Usage:

`lake env lean --run examples/accompaniment.lean | alda import -i musicxml | alda play --wait`
-/
def main : IO UInt32 := do
  let score := compose generateAccompaniment (src := Example.necrofantasia) |>.run
  IO.eprintln s!"{score}"
  let xml := score.toMusicXML
  IO.println s!"{xml}"
  return 0
