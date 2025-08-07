import Prismriver.Repr.Scale

namespace Prismriver.Classical

/-- Accidental measured in terms of the number of semitones from natural. -/
structure Accidental where
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

/-- This represents the name of a note in the heptatonic scale. -/
inductive Hep where
  | a
  | b
  | c
  | d
  | e
  | f
  | g
  deriving BEq, Inhabited

instance : ToString Hep where
  toString
    | .a => "a"
    | .b => "b"
    | .c => "c"
    | .d => "d"
    | .e => "e"
    | .f => "f"
    | .g => "g"

/-- The name of the scale when all notes are ♮ and when the scale's root starts
on some particular note. For example, a scale `d e f g a b c` is Dorian. -/
protected def Hep.modus : Hep → String
  | .c => "major" -- also ionian
  | .d => "dorian"
  | .e => "phrygian"
  | .f => "lydian"
  | .g => "mixolydian"
  | .a => "minor" -- also aeolian
  | .b => "locrian"
instance : Coe Hep (Fin 7) where
  coe
    | .c => 2
    | .d => 3
    | .e => 4
    | .f => 5
    | .g => 6
    | .a => 0
    | .b => 1
instance : Coe (Fin 7) Hep where
  coe
    | 0 => .a
    | 1 => .b
    | 2 => .c
    | 3 => .d
    | 4 => .e
    | 5 => .f
    | 6 => .g
protected def Hep.toNat (h : Hep) := (h : Fin 7).toNat

structure Tone where
  name : Hep
  acc : Accidental := .natural
  deriving BEq, Inhabited

instance : ToString Tone where
  toString t := if t.acc == .natural then toString t.name else s!"{t.name}{t.acc}"
instance : Coe Hep Tone where
  coe name := { name }

instance : ToString (Pitch Tone) where
  toString p := s!"{p.tone}{p.n}"

def spaces := [2, 1, 2, 2, 1, 2, 2]

instance diatonic (root : Tone) (modus : Hep) : Scale Tone where
  name := s!"{root} {modus.modus}"
  tones := List.finRange 7 |>.map λ i =>
    let name := i.add root.name
    -- Nominal shift if the letters are read directly with the same accidentals
    let shiftNominal := (root.name : Fin 7).toNat.repeat List.rotateLeft spaces
      |>.take i.toNat |>.sum
    -- Actual shift determined by modus
    let shiftModus := (modus : Fin 7).toNat.repeat List.rotateLeft spaces
      |>.take i.toNat |>.sum
    { name, acc := ⟨shiftModus - shiftNominal + root.acc.semitones⟩ }

instance diatonicLift root modus : ScaleLift Tone EqualTemp.Tone12 (src := diatonic root modus) (dst := EqualTemp.et12) where
  liftPitch pitch :=
    -- Nominal shift if the letters are read directly with the same accidentals
    let shiftNominal := (root.name : Fin 7).toNat.repeat List.rotateLeft spaces
      |>.take pitch.tone.name.toNat |>.sum
    let total := shiftNominal + pitch.tone.acc.semitones
    let Δoct := Int.fdiv total 12
    let semi := Int.fmod total 12 |>.toNat
    have : semi < 12 := by
      sorry
    -- FIXME: Calculate proper offset
    { n := pitch.n + Δoct, tone := ⟨semi, ‹semi < 12›⟩ }
