import Prismriver.Repr.Pitch

namespace Prismriver.Classical

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


theorem toString_zero_semitones (a : Accidental) (h : a.semitones = 0) :
  toString a = "♮" := by
  unfold toString
  unfold instToStringAccidental
  simp only []
  rw [h]
  simp


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
  toString t := if t.acc == .natural then toString t.name else s!"{t.name}{t.acc}"
instance : Coe Oct Tone where
  coe name := { name }

structure Pitch extends Tone where
  octave : Int
  deriving BEq, Inhabited

instance : ToString Pitch where
  toString p := s!"{p.toTone}{p.octave}"

def spaces := [2, 1, 2, 2, 1, 2, 2]

instance diatonic (root : Tone) (modus : Oct) : Scale Pitch where
  name := s!"{root} {modus.modus}"
  notes octave := List.finRange 7 |>.map λ i =>
    let name := i.add root.name
    -- Nominal shift if the letters are read directly with the same accidentals
    let shiftNominal := (root.name : Fin 7).toNat.repeat List.rotateLeft spaces
      |>.take i.toNat |>.sum
    -- Actual shift determined by modus
    let shiftModus := (modus : Fin 7).toNat.repeat List.rotateLeft spaces
      |>.take i.toNat |>.sum
    { octave, name, acc := ⟨shiftModus - shiftNominal + root.acc.semitones⟩ }

instance diatonicLift root modus : ScaleLift Pitch ET12.Pitch (src := diatonic root modus) (dst := ET12.instScalePitch) where
  lift p :=
    -- FIXME: Calculate proper offset
    { octave := p.octave, offset := 0 }

-- Examples
#eval (⟨.c, .natural⟩: Tone)
#eval (⟨.d, .sharp⟩: Tone)
#eval ({ name :=.d, octave := 4 }: Pitch)
#eval (diatonic ⟨.e, .sharp⟩ .d).name
#eval (diatonic ⟨.d, .natural⟩ .a).notes 5
#eval (diatonic ⟨.f, .natural⟩ .d).notes 5
