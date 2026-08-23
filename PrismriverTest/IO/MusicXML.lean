import Prismriver.IO.MusicXML
import Prismriver.Composition.Basic
import PrismriverTest.Common

namespace Prismriver.Test.IO.MusicXML

open Lean

open Prismriver.Classical Prismriver.Composition in
def test_division : TestT IO Unit := do
  let score := compose compositionM |>.run
  let .ok xml := Xml.parse $ toString score.toMusicXML | panic "failed"

  let file ← IO.FS.readFile "./PrismriverTest/IO/example.xml"
  let .ok elem := Xml.parse file | panic "failed"
  checkTrue "xml" (elem == xml)
  --IO.FS.writeFile "/tmp/example.xml" s!"{xml}"
  where
  compositionM : Classical.CompositionT Id Unit := do
    addPart 0 { instrument? := .some Instrument.violin }
    let t14 : MeasuredTime := mkRat 1 4
    let t11 : MeasuredTime := mkRat 1 1
    addPianoNote ⟨.new .e 4, t14⟩
    addPianoNote ⟨.new .c 5, t14⟩
    addPianoNote ⟨.new .b 4, t14⟩
    addPianoNote ⟨.new .d 4, t14⟩
    move .bar
    addPianoNote ⟨.new .e 4, t11⟩
  addPianoNote (note: Classical.Note)
    : Classical.CompositionT Id Unit :=
    addNote note (partId? := .some 0)

def suite : List (String × IO LSpec.TestSeq) := [
    ("division", runTest test_division)
  ]
