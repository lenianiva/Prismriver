namespace Prismriver

/-- A set of permitted notes -/
class PseudoScale (P : Type) where
  name : String
  -- The list of all permitted notes on the scale. For periodic scales this should return empty
  allNotes : List P := []

class PseudoScaleLift (P₁ P₂ : Type) (src : PseudoScale P₁) (dst : PseudoScale P₂) where
  lift : P₁ → P₂

/-- A scale with a repeating fundamental interval -/
class Scale (P : Type) extends PseudoScale P where
  -- List all notes in the n₀th interval (usually an octave)
  notes (n₀ : Int) : List P

class ScaleLift (P₁ P₂ : Type) (src : Scale P₁) (dst : Scale P₂)
  extends PseudoScaleLift P₁ P₂ src.toPseudoScale dst.toPseudoScale where

namespace ET12

structure Pitch where
  octave : Int
  offset : Fin 12

instance : Scale Pitch where
  name := "12-ET"
  notes octave := Fin.foldl (n := 12) (init := []) λ acc offset =>
    { octave, offset } :: acc

end ET12

