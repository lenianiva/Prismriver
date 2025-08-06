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

protected def Accidental.natural : Accidental := ⟨0⟩
protected def Accidental.sharp : Accidental := ⟨1⟩
protected def Accidental.flat : Accidental := ⟨-1⟩

instance : ToString Accidental where
  toString a :=
    if a.semitones == 0 then
      "♮"
    else
      let sign := a.semitones > 0
      let one := if sign then "♯" else "♭"
      let n := Int.natAbs a.semitones
      String.join (List.replicate n one)

inductive Oct where
  | a
  | b
  | c
  | d
  | e
  | f
  | g
  deriving BEq, Inhabited

instance : ToString Oct where
  toString
    | .a => "a"
    | .b => "b"
    | .c => "c"
    | .d => "d"
    | .e => "e"
    | .f => "f"
    | .g => "g"

protected def Oct.modus : Oct → String
  | .c => "major" -- also ionian
  | .d => "dorian"
  | .e => "phrygian"
  | .f => "lydian"
  | .g => "mixolydian"
  | .a => "minor" -- also aeolian
  | .b => "locrian"
instance : Coe Oct (Fin 7) where
  coe
    | .c => 2
    | .d => 3
    | .e => 4
    | .f => 5
    | .g => 6
    | .a => 0
    | .b => 1
instance : Coe (Fin 7) Oct where
  coe
    | 0 => .a
    | 1 => .b
    | 2 => .c
    | 3 => .d
    | 4 => .e
    | 5 => .f
    | 6 => .g

structure Tone where
  name : Oct
  acc : Accidental := .natural
  deriving BEq, Inhabited

instance : ToString Tone where
  toString t := s!"{t.name}{t.acc}"
instance : Coe Oct Tone where
  coe name := { name }

structure Pitch (modus : Oct) (root : Tone) extends Tone where
  octave : Int
  deriving BEq, Inhabited

instance : ToString (Pitch modus root)  where
  toString p := s!"{p.toTone}{p.octave}"


instance : Scale (Pitch modus root) where
  notes octave := Fin.foldl (n := 7) (init := []) λ acc name =>
    { octave, name } :: acc

instance : ScaleLift (Pitch modus root) ET12.Pitch where
  lift p :=
    -- FIXME: Calculate proper offset
    { octave := p.octave, offset := 0 }

-- Examples
#eval (⟨.c, .natural⟩: Tone)
#eval (⟨.d, .sharp⟩: Tone)
#eval ({ name :=.d, octave := 4 }: (Pitch .d Oct.g))

end Classical
