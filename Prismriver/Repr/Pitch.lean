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
  lift : P₁ → P₂

/-- A scale with a repeating fundamental interval -/
class Scale (P : Type) extends PseudoScale P where
  /-- List all notes in the n₀th interval (usually an octave) -/
  pitches (n₀ : Int) : List P

class ScaleLift (P₁ P₂ : Type) (src : Scale P₁) (dst : Scale P₂)
  extends PseudoScaleLift P₁ P₂ src.toPseudoScale dst.toPseudoScale where

namespace ET12

structure Pitch where
  octave : Int
  offset : Fin 12

instance scale : Scale Pitch where
  name := "12-ET"
  pitches octave := List.finRange 12 |>.map λ offset =>
    { octave, offset }

theorem et12_notes (octave : Int) : (scale.pitches octave).length = 12 := by
  rfl

end ET12

