import Prismriver.Repr.Score

import Lean.Data.Xml
import Lean.Data.RBMap

open Lean

namespace Prismriver

structure Metadata where
  title : String := "untitled"
  deriving Inhabited

private def single (name s : String) : Xml.Element := .Element
    (name := name)
    (attributes := .empty)
    (content := #[.Character s])

protected def Metadata.toWorkElement (metadata : Metadata) : Xml.Element :=
  let content := #[
    .Element (single "work-title" $ metadata.title),
  ]
  .Element
    (name := "work")
    (attributes := .empty)
    (content := content)

protected def Part.toMusicXML (_part : Classical.Part) (id : PartId) : Xml.Element :=
  let midiInstrument := .Element
    (name := "midi-instrument")
    (attributes := (.empty : Xml.Attributes).insert "id" "part1-i1")
    (content := #[
    .Element (single "midi-program" $ toString 1)
  ])
  let content := #[
    .Element (single "part-name" "part1"),
    .Element midiInstrument,
  ]
  .Element
    (name := "score-part")
    (attributes := (.empty : Xml.Attributes).insert "id" $ toString id)
    (content := content)

protected def Pitch.toMusicXML (pitch : Classical.Pitch) : Xml.Element :=
  let content := #[
    .Element (single "step" $ (toString pitch.hep).toUpper),
    .Element (single "octave" $ toString pitch.octave),
  ]
  let ⟨acc⟩ := pitch.acc
  let content := if acc != 0 then
      content ++ [Xml.Content.Element (single "alter" $ toString acc)]
    else
      content
  .Element
    (name := "pitch")
    (attributes := .empty)
    (content := content)

/-- Convert a note -/
protected def Note.toMusicXML (note : Classical.Note) (duration : Nat) : Xml.Element :=
  let content := #[
    .Element (Pitch.toMusicXML note.pitch),
    .Element (single "duration" $ toString duration),
    .Element (single "type" "quarter"),
    .Element (single "voice" $ toString 1),
  ]
  .Element
    (name := "note")
    (attributes := .empty)
    (content := content)

private def rest (duration : Nat) : Xml.Element :=
  let content := #[
    .Element (.Element (name := "rest") .empty #[]),
    .Element (single "duration" $ toString duration),
    .Element (single "type" "quarter"),
    .Element (single "voice" $ toString 1),
  ]
  .Element
    (name := "note")
    (attributes := .empty)
    (content := content)

private def backup (duration : Nat) : Xml.Element :=
  let content := #[
    .Element (single "duration" $ toString duration),
  ]
  .Element
    (name := "backup")
    (attributes := .empty)
    (content := content)

private structure Measure where
  notes : List (MeasuredTime × Classical.Note) := []

/-- Guarded LCM -/
private def glcm : Nat → Nat → Nat
  | 0,n => n
  | n,0 => n
  | n,m => n.lcm m

protected def Measure.toMusicXML (measure : Measure) (number : Nat) : Xml.Element :=
  -- determine minimal number of divisions of quarter notes
  let divisions := measure.notes.foldl (init := (4 : Nat)) λ d (time, { duration, .. }) =>
    glcm (glcm duration.offset.den d) time.offset.den

  let header := .Element
    (name := "attributes")
    (attributes := .empty)
    (content := #[
    .Element (single "divisions" $ toString (divisions / 4)),
  ])
  let contentM : StateM Nat (List Xml.Content) := measure.notes.foldlM (init := [.Element header])
    λ elements (time, note) => do
    let t := (time.offset * divisions).num.toNat
    let d := (note.duration.offset * divisions).num.toNat
    -- Insert necessary backoff
    let current ← get
    let pad := if t = current then
        []
      else if t < current then
        [.Element (backup (current - t))]
      else
        [.Element (rest (t - current))]
    -- Insert note itself
    let notes := [.Element (note.toMusicXML d)]
    -- Move the time
    modify (· + d)
    pure (elements ++ pad ++ notes)

   let content := contentM.run' 0

  .Element
    (name := "measure")
    (attributes := (.empty : Xml.Attributes).insert "number" $ toString number)
    (content := content.toArray)

private structure OutputState where
  time : MeasuredTime := {}
  /-- Measure number -/
  measureN : Nat := 0
  parts : Std.TreeMap PartId (Std.TreeMap Nat Measure)
  measure : List Classical.Note := []

private def OutputState.insertNote (σ : OutputState) (partId : PartId)
  (time : MeasuredTime) (elem : Classical.Note) : OutputState :=
  let es := [(time, elem)]
  {
    σ with
    parts := σ.parts.modify partId λ part => part.alter σ.measureN λ
      | .none => .some { notes := es }
      | .some measure => .some { notes := measure.notes ++ es }
  }

/-- Export a score to timewise MusicXML form -/
protected def Score.toMusicXML (score : Classical.Score) (metadata : Metadata := {})
  : Xml.Element :=
  let partsM : StateM OutputState Unit := score.forM (P := Classical.Pitch)
    λ context@{ time, .. } => do
    let σ ← get
    if σ.time.bars ≠ time.bars then
      modify λ σ => { σ with measureN := time.bars.toNat }
    context.newEvents.forM λ
      | .note _ .none => pure ()
      | .note note (.some partId) =>
        modify (OutputState.insertNote · partId time note)
      | _ => pure ()

  let (_, outputState) := partsM.run {
      parts := score.parts.keys.foldl (init := .empty) λ acc key => acc.insert key .empty
    }
    --|>.map (Xml.Content.Element ·)

  let parts := outputState.parts.foldl (init := #[]) λ parts partId part =>
    let content := part.foldl (init := #[]) λ measures measureNumber measure =>
      let element := measure.toMusicXML measureNumber
      measures ++ #[.Element element]
    let element := .Element
      (name := "part")
      (attributes := (.empty : Xml.Attributes).insert "id" $ toString partId)
      (content := content)
    parts ++ #[.Element element]
  let partList : Array Xml.Content := score.parts.foldl (init := #[]) λ acc id part =>
    let elem := .Element (part.toMusicXML id)
    acc ++ #[elem]
  let rootContent : Array Xml.Content := #[
    Xml.Content.Element (metadata.toWorkElement),
    .Element (.Element
      (name := "part-list")
      (attributes := .empty)
      (content := partList)
    ),
  ] ++ parts

  Xml.Element.Element
    (name := "score-partwise")
    (attributes := (.empty : Xml.Attributes).insert "version" "3.1")
    (content := rootContent)
