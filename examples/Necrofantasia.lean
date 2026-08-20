import Prismriver.Repr
import Prismriver.IO
import Prismriver.Composition.Basic

open Prismriver Prismriver.Classical Prismriver.Composition

def addPianoNote (note: Classical.Note)
  : Classical.CompositionT Id Unit := addNote note (partId? := .some 0)

def compositionM : Classical.CompositionT Id Unit := do
  addPart 0 { instrument? := .some Instrument.violin }
  let t14 : MeasuredTime := mkRat 1 4
  let t11 : MeasuredTime := mkRat 1 1
  addEvent (.control (.key 0))
  addPianoNote ⟨.new .e 4, t14⟩
  addPianoNote ⟨.new .c 5, t14⟩
  addPianoNote ⟨.new .b 4, t14⟩
  addPianoNote ⟨.new .d 4, t14⟩
  move .bar
  addPianoNote ⟨.new .e 4, t11⟩

/--
Usage:

`lake env lean --run examples/Necrofantasia.lean | alda import -i musicxml | alda play`
-/
def main : IO UInt32 := do
  let score := compose compositionM |>.run
  IO.eprintln s!"{score}"
  let xml := score.toMusicXML
  IO.println s!"{xml}"
  return 0
