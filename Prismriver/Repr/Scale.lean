namespace Prismriver

/-- A set of permitted pitches -/
class PseudoScale (P : Type) where
  name : String
  isFinite : Bool := false
  /-- The list of all permitted notes on the scale. For periodic and infinite
  scales this should return empty -/
  allNotes : List P := []

/-- We make no distinction between scales and tuning systems. They are
represented by the same class. For example, a tuning system could be represented
as a scale with raw frequencies, and any abstract scale could be lifted into the
raw frequency scale. This would represent tuning. -/
class PseudoScaleLift (P₁ P₂ : Type) (src : PseudoScale P₁) (dst : PseudoScale P₂) where
  liftPitch : P₁ → P₂

/-- In most scales, a pitch would be a tone (e.g. C♯) along with a multiple of
the fundamental interval, which is often an octave. -/
structure Pitch (T : Type) where
  tone : T
  -- Offset in terms of the fundamental interval
  n : Int

/-- A scale with a repeating fundamental interval. Each pitch in the scale is
represented as a tone along with a multiple of the fundamental interval. -/
class Scale (T : Type) extends PseudoScale (Pitch T) where
  isFinite := false
  /-- List all notes in the n₀th interval (usually an octave) -/
  tones : List T

class ScaleLift (T₁ T₂ : Type) (src : Scale T₁) (dst : Scale T₂)
  extends PseudoScaleLift (Pitch T₁) (Pitch T₂) src.toPseudoScale dst.toPseudoScale where

class ToneLift (T₁ T₂ : Type) (src : Scale T₁) (dst : Scale T₂)
  extends ScaleLift T₁ T₂ src dst where
  liftTone : T₁ → T₂
  liftPitch p := { p with tone := liftTone p.tone }

namespace EqualTemp

abbrev Tone (n : Nat) := Fin n

instance scale (n : Nat) : Scale (Tone n) where
  name := s!"{n}-ET"
  tones := List.finRange n

theorem et_notes (n : Nat) : (scale n).tones.length = n :=
  List.length_finRange

abbrev et12 := scale 12
abbrev Tone12 := Tone 12

end EqualTemp
