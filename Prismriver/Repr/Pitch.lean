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

namespace Classical

structure Accidental where
  -- offset in terms of semitones
  semitones : Int := 0
  deriving BEq, Inhabited

instance : ToString Accidental where
  toString a :=
    let sign := a.semitones > 0
    let one := if sign then "♯" else "♭"
    let n := Int.natAbs a.semitones
    String.join (List.replicate n one)

inductive Modus where
  | major -- also ionian
  | dorian
  | phrygian
  | lydian
  | mixolydian
  | minor -- also aeolian
  | locrian

structure Pitch (modus : Modus) where
  octave : Int
  offset : Fin 7
  acc : Accidental := ⟨0⟩
  deriving BEq, Inhabited

instance (modus : Modus) : Scale (Pitch modus) where
  notes octave := Fin.foldl (n := 7) (init := []) λ acc offset =>
    { octave, offset } :: acc

instance (modus : Modus) : ScaleLift (Pitch modus) ET12.Pitch where
  lift p :=
    -- FIXME: Calculate proper offset
    { octave := p.octave, offset := 0 }

end Classical
