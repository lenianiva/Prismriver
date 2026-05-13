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
  let notes : Array Xml.Content := Id.run $ score.foldM (P := Classical.Pitch)
    (init := #[]) (m := λ notes { events, .. } => do
    let newNotes := events.filterMap λ
      | .note note _instrument? =>
        .some $ Xml.Content.Element note.toMusicXML
      | _ => .none
    return notes ++ newNotes)

  let measures : Array Xml.Content := #[
    .Element (.Element
      (name := "measure")
      (attributes := (.empty : Xml.Attributes).insert "number" "1")
      (content := #[
        .Element (.Element
          (name := "part")
          (attributes := (.empty : Xml.Attributes).insert "id" "part1")
          (content := notes)
        )
      ])
    ),
  ]
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
