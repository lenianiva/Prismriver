namespace Prismriver

/-- A scale with a particular fundamental harmonic ratio and pitch type -/
class Scale (P : Type) where
  -- List all notes in the n₀th interval (usually an octave)
  notes (n₀ : Int) : List P

class ScaleLift (P₁ P₂ : Type) [Scale P₁] [Scale P₂] where
  lift : P₁ → P₂

namespace ET12

structure Pitch where
  octave : Int
  offset : Fin 12

instance : Scale Pitch where
  notes octave := Fin.foldl (n := 12) (init := []) λ acc offset =>
    { octave, offset } :: acc

end ET12

