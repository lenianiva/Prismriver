import Prismriver.Repr.Score

import Lean.Data.Xml
import Lean.Data.RBMap

open Lean

namespace Prismriver

structure Metadata where
  title : String := "untitled"
  deriving Inhabited

namespace Xml

def single (name s : String) : Xml.Element := .Element
    (name := name)
    (attributes := .empty)
    (content := #[.Character s])

private structure OutputState where
  time : MeasuredTime := {}
  measure : List Classical.Note := []
  /-- Measure number -/
  measureN : Nat := 0

private def OutputState.packMeasure (σ : OutputState) (time : MeasuredTime)
  : (OutputState × List Classical.Note) :=
  let σ' := {
    σ with
    time,
    measure := []
    measureN := σ.measureN + 1
  }
  (σ', σ.measure)

end Xml

open Prismriver.Xml

/-- Convert a note -/
protected def Note.toMusicXML (note : Classical.Note) : Xml.Element :=
  let content := #[
    .Element (.Element
      (name := "pitch")
      (attributes := .empty)
      (content := #[
        .Element (single "step" $ toString note.pitch.hep),
        .Element (single "octave" $ toString note.pitch.octave),
      ])
    ),
    .Element (single "duration" $ toString note.duration),
    .Element (single "type" "whole"),
  ]
  .Element
    (name := "note")
    (attributes := .empty)
    (content := content)

/-- Export a score to timewise MusicXML form -/
protected def Score.toMusicXML (score : Classical.Score) (metadata : Metadata := {})
  : Xml.Element :=
  let measuresM : StateM OutputState (Array Xml.Element) := score.foldM (P := Classical.Pitch)
    (init := #[]) (m := λ acc { time, events } => do
    let σ ← get
    let newMeasure ← if σ.time.bar ≠ time.bar then
        let (σ', measureNotes) := σ.packMeasure time
        let attrs := (.empty : Xml.Attributes).insert "number" (toString σ.measureN)
        set σ'
        let measure := Xml.Element.Element
          (name := "measure")
          (attributes := attrs)
          (content := #[
            .Element (.Element
              (name := "part")
              (attributes := (.empty : Xml.Attributes).insert "id" "part1")
              (content := measureNotes.toArray.map (.Element ·.toMusicXML))
            )
          ])
        pure #[measure]
      else
        --
        let newNotes := events.filterMap λ
          | .note note _instrument? =>
            .some note
          | _ => .none
        modify λ state ↦ { state with measure := state.measure ++ newNotes }
        pure #[]
      -- consolidate another bar
    return acc ++ newMeasure)

  let measures : Array Xml.Content := measuresM.run' {}
    |>.map (Xml.Content.Element ·)

  let partList : Array Xml.Content := #[
    .Element (single "part-name" "part1"),
    .Element (single "id" "part1"),
  ]
  let rootContent : Array Xml.Content := #[
    .Element (.Element
      (name := "movement-title")
      (attributes := .empty)
      (content := #[.Character metadata.title])
    ),
    .Element (.Element
      (name := "part-list")
      (attributes := .empty)
      (content := partList)
    ),
  ] ++ measures

  Xml.Element.Element
    (name := "score-timewise")
    (attributes := (.empty : Xml.Attributes).insert "version" "4.0")
    (content := rootContent)
