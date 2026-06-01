-- Random chord progression
import Prismriver.Composition.ChordProgression
import Prismriver.IO.MusicXML

open Prismriver Composition

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
