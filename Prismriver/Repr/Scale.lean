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
class Tuning (P₁ P₂ : Type) (src : PseudoScale P₁) (dst : PseudoScale P₂) where
  liftPitch : P₁ → P₂

/-- A scale with a repeating fundamental interval. Each pitch in the scale is
represented as a tone along with a multiple of the fundamental interval. -/
class Scale (P I : Type) [HAdd P I P] extends PseudoScale P where
  isFinite := false
  /-- The fundamental interval (usually an octave) -/
  fundamental : I
  /-- List all notes in the 0th interval. e.g. For C major, this would be C,D,E,F,G,A,B -/
  pitches : List P

namespace EqualTemp

abbrev Pitch := Int
abbrev Interval := Int

instance scale (n : Nat) : Scale Pitch Interval where
  name := s!"{n}-ET"
  fundamental := n
  pitches := List.finRange n |>.map (·.toNat)

theorem n_et_notes (n : Nat) : (scale n).pitches.length = n := by
  unfold Scale.pitches
  unfold scale
  rewrite [List.length_map]
  apply List.length_finRange

abbrev et12 := scale 12

end EqualTemp

export EqualTemp (et12)
