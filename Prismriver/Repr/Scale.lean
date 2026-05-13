import Lean

namespace Prismriver

/-- A scale is a set of pitches -/
class PseudoScale (P : Type) where
  name : String

/-- We make no distinction between scales and tuning systems. They are
represented by the same class. For example, a tuning system could be represented
as a scale with raw frequencies, and any abstract scale could be lifted into the
raw frequency scale. This would represent tuning. -/
class Tuning (P₁ P₂ : Type) (src : PseudoScale P₁) (dst : PseudoScale P₂) where
  liftPitch : P₁ → P₂

/-- A scale with a repeating fundamental interval. Each pitch in the scale is
represented as a tone along with a multiple of the fundamental interval. -/
class Scale (P) extends PseudoScale P where
  I : Type
  hAdd : HAdd P I P
  hSub : HSub P P I
  /-- The fundamental interval (usually an octave) -/
  fundamental : I
  /-- List all notes in the 0th interval. e.g. For C major, this would be C,D,E,F,G,A,B -/
  pitches : List P

namespace EqualTemp

abbrev Pitch := Int
abbrev Interval := Int

instance scale (n : Nat) : Scale Pitch where
  I := Interval
  hAdd := @instHAdd Int Int.instAdd
  hSub := @instHSub Int Int.instSub
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
