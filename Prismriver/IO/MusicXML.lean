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

protected def Part.toMusicXML (part : Part) (id : PartId) : Xml.Element :=
  let midiInstrument := match part.instrument?.bind (·.midiInstrument?) with
    | .none => #[]
    | .some program =>
      #[
        .Element (.Element
            (name := "midi-instrument")
            (attributes := (.empty : Xml.Attributes).insert "id" s!"part{id}-{program}")
            (content := #[
            .Element (single "midi-program" $ toString program)
          ]))
      ]
  let partName := match part.instrument? with
    | .some i => i.name
    | .none => toString id
  let content := #[
    .Element (single "part-name" partName),
  ] ++ midiInstrument
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

/-- Convert a note to MusicXML using a common divisions number -/
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

protected def Event.toMusicXML (event : Classical.Event) (duration : Nat)
  : Option Xml.Element := match event with
  | .note n _ => n.toMusicXML duration
  | .control (.fifth n) => .some <| .Element
      (name := "")
      (attributes := .empty)
      (content := #[
        .Element (single "fifth" $ toString n)
      ])
  | .control .wall => .none

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
  -- List of all events in the measure
  events : List (MeasuredTime × Classical.Event) := []

/-- Guarded LCM which hands 0's as a passthrough case -/
private def glcm : Nat → Nat → Nat
  | 0,n => n
  | n,0 => n
  | n,m => n.lcm m

protected def Measure.toMusicXML (measure : Measure) (number : Nat) : Xml.Element :=
  -- determine minimal number of divisions of quarter notes
  let divisions := measure.events.foldl (init := (4 : Nat)) λ d (time, event) =>
    match event.duration? with
    | .some duration => glcm (glcm duration.offset.den d) time.offset.den
    | .none => glcm d time.offset.den

  let header := .Element
    (name := "attributes")
    (attributes := .empty)
    (content := #[
    .Element (single "divisions" $ toString (divisions / 4)),
  ])
  let contentM : StateM Nat (List Xml.Content) := measure.events.foldlM (init := [.Element header])
    λ elements (time, event) => do
    let t := (time.offset * divisions).num.toNat
    let d := event.duration?.map (λ (duration : MeasuredTime) => (duration.offset * divisions).num.toNat) |>.getD 0
    -- Insert necessary backoff
    let current ← get
    let pad := if t = current then
        []
      else if t < current then
        [.Element (backup (current - t))]
      else
        [.Element (rest (t - current))]
    -- Insert note itself
    let notes := match event.toMusicXML divisions with
      | .some elem => [.Element elem]
      | .none => []
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

/-- If a part id is not specified, insert into all parts -/
private def OutputState.insertEvent (σ : OutputState)
  (time : MeasuredTime) (event : Classical.Event) : OutputState :=
  let es := [(time, event)]
  let parts := match event.partId? with
    | .some partId => σ.parts.modify partId λ part => part.alter σ.measureN λ
      | .none => .some { events := es }
      | .some measure => .some { events := measure.events ++ es }
    | .none => σ.parts.map λ _partId part => part.alter σ.measureN λ
      | .none => .some { events := es }
      | .some measure => .some { events := measure.events ++ es }
  {
    σ with
    parts
  }

/-- Export a score to timewise MusicXML form -/
protected def Score.toMusicXML (score : Classical.Score) (metadata : Metadata := {})
  : Xml.Element :=
  let partsM : StateM OutputState Unit := score.forM (P := Classical.Pitch)
    λ context@{ time, .. } => do
    let σ ← get
    if σ.time.bars ≠ time.bars then
      modify λ σ => { σ with measureN := time.bars.toNat }
    context.newEvents.forM λ e =>
      modify (OutputState.insertEvent · time  e)

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
