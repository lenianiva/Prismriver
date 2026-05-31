import Prismriver.Repr
import Prismriver.IO
import Prismriver.Composition.Basic

open Prismriver Prismriver.Classical Prismriver.Composition

def compositionM : Classical.CompositionT Id Unit := do
  let t14 : MeasuredTime := mkRat 1 4
  addNote ⟨.new .c 4, t14⟩
  addNote ⟨.new .d 4, t14⟩
  addNote ⟨.new .e 4, t14⟩
  addNote ⟨.new .f 4, t14⟩

/--
Usage:

`lake env lean --run examples/XML.lean | alda import -i musicxml | alda play`
-/
def main : IO UInt32 := do
  let (_, { score, .. }) := compositionM.run {} |>.run
  IO.eprintln s!"{score}"
  let xml := score.toMusicXML
  IO.println s!"{xml}"
  return 0
