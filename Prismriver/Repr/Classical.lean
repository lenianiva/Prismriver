import Prismriver.Repr.Scale
import Prismriver.Repr.Note

import Lean.ToExpr

namespace Prismriver.Classical

/-- Accidental measured in terms of the number of semitones from natural. -/
structure Accidental where
  semitones : Int := 0
  deriving BEq, Inhabited

open Lean in
instance : ToExpr Accidental where
  toExpr a :=
    let semitones := toExpr a.semitones
    mkAppN (mkConst ``Accidental.mk) #[semitones]
  toTypeExpr : Expr := mkConst ``Accidental
instance : ToString Accidental where
  toString a :=
    if a.semitones == 0 then
      "♮"
    else
      let sign := a.semitones > 0
      let one := if sign then "♯" else "♭"
      let n := Int.natAbs a.semitones
      String.join (List.replicate n one)

namespace Accidental

protected def natural : Accidental := ⟨0⟩
protected def sharp : Accidental := ⟨1⟩
protected def flat : Accidental := ⟨-1⟩

protected def toSuffix : Accidental → String
  | ⟨0⟩ => ""
  | a => toString a

instance : Add Accidental where
  add x y := { semitones := x.semitones + y.semitones }
instance : Sub Accidental where
  sub x y := { semitones := x.semitones - y.semitones }
instance : SMul Int Accidental where
  smul n x := { semitones := n * x.semitones }

end Accidental

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
    | .c => 0
    | .d => 1
    | .e => 2
    | .f => 3
    | .g => 4
    | .a => 5
    | .b => 6
instance : Coe (Fin 7) Hep where
  coe
    | 0 => .c
    | 1 => .d
    | 2 => .e
    | 3 => .f
    | 4 => .g
    | 5 => .a
    | 6 => .b
protected def Hep.toNat (h : Hep) := (h : Fin 7).toNat

/-- Semitone spaces between names -/
def spaces := [2, 2, 1, 2, 2, 2, 1]

structure Tone where
  name : Hep
  acc : Accidental := .natural
  deriving BEq, Inhabited

instance : ToString Tone where
  toString t := if t.acc == .natural then toString t.name else s!"{t.name}{t.acc}"

structure Pitch where
  name : Int
  acc : Accidental := .natural
  deriving BEq, Inhabited

protected def Pitch.new (hep : Hep) (octave : Int) (acc : Accidental := .natural) : Pitch :=
  { name := hep.toNat + octave * 7, acc }
protected def Pitch.hep (p : Pitch) : Hep :=
  let fin : Fin 7 := Fin.intCast p.name
  fin
protected def Pitch.tone (p : Pitch) : Tone :=
  { name := p.hep, acc := p.acc }
protected def Pitch.octave (p : Pitch) : Int :=
  Int.fdiv p.name 7

instance : ToString Pitch where
  toString t := s!"{t.tone}{t.octave}"

open Lean in
instance : ToExpr Pitch where
  toExpr p :=
    let name := toExpr p.name
    let acc := toExpr p.acc
    mkAppN (mkConst ``Pitch.mk) #[name, acc]
  toTypeExpr : Expr := mkConst ``Pitch

namespace Pitch

protected def c4 : Pitch := ⟨7 * 4, .natural⟩

end Pitch

/-- An interval consists of a letter distance and a semitone distance -/
structure Interval where
  name : Int
  semitones : Int
  deriving BEq, Inhabited

private def nameDistanceAux (total : Nat) (key : Hep) : Nat → Nat
  | 0 => total
  | remainder+1 =>
    let key' : Fin 7 := key
    let total' := total + spaces[key']
    nameDistanceAux total' (key' + (1 : Fin 7)) remainder

/-- Calculates the semitone distance of `n2 - n1` two pitches with no accidentals -/
def nameDistance (n2 n1 : Int) : Int :=
  if n1 ≤ n2 then
    let fin : Fin 7 := Fin.intCast n1
    nameDistanceAux 0 fin (Int.toNat (n2 - n1))
  else
    let fin : Fin 7 := Fin.intCast n2
    let d : Int := nameDistanceAux 0 fin (Int.toNat (n1 - n2))
    (-d : Int)

instance : HSub Pitch Pitch (outParam Interval) where
  hSub p1 p2 :=
    let Δname := nameDistance p1.name p2.name
    let Δacc := p1.acc - p2.acc
    { name := p1.name - p2.name, semitones := Δname + Δacc.semitones }
/-- Group action of interval group on the set of pitches -/
instance : HAdd Pitch Interval Pitch where
  hAdd p i :=
    let name := p.name + i.name
    -- Semitones accounted for in the name with no accidentals
    let Δsemitones := nameDistance name p.name
    { name, acc := { semitones := i.semitones - Δsemitones} }
instance : Neg Interval where
  neg i := { name := -i.name, semitones := -i.semitones }

namespace Interval

def octave : Interval := { name := 7, semitones := 12 }
def unison : Interval := ⟨0, 0⟩
def mi2 : Interval := ⟨1, 1⟩
def ma2 : Interval := ⟨1, 2⟩
def mi3 : Interval := ⟨2, 3⟩
def ma3 : Interval := ⟨2, 4⟩
def p4 : Interval := { name := 3, semitones := 5 }
def p5 : Interval := { name := 4, semitones := 7 }
def mi6 : Interval := ⟨5, 8⟩
def ma6 : Interval := ⟨5, 9⟩
def mi7 : Interval := ⟨6, 10⟩
def ma7 : Interval := ⟨6, 11⟩

instance : Coe Accidental Interval where
  coe acc := { acc with name := 0}

inductive Quality
  | p (semitones : Nat)
  | mM (minorSemitones majorSemitones : Nat)

def intervalNames : List Quality :=
  [.p 0, .mM 1 2, .mM 3 4, .p 5, .p 7, .mM 8 9, .mM 10 11]

instance : ToString Interval where
  toString i :=
    let h : Fin 7 := Fin.intCast i.name
    let octaves := Int.fdiv i.name 7
    match intervalNames[h] with
    | .p 0 =>
      let head := if octaves == 0 then "u" else "{octaves}o"
      let acc : Accidental := ⟨i.semitones - 12 * octaves⟩
      s!"{head}{acc.toSuffix}"
    | .p semitones =>
      let acc : Accidental := ⟨i.semitones - semitones - 12 * octaves⟩
      s!"P{i.name+1}{acc.toSuffix}"
    | .mM minorSemitones majorSemitones =>
      let nominalSemitones := i.semitones - 12 * octaves
      let (marker, semitones) :=
        if nominalSemitones ≤ minorSemitones then
          ("m", minorSemitones)
        else
          ("M", majorSemitones)
      let acc : Accidental := ⟨nominalSemitones - semitones⟩
      s!"{marker}{i.name+1}{acc.toSuffix}"

instance : Add Interval where
  add x y := { name := x.name + y.name, semitones := x.semitones + y.semitones }
instance : Sub Interval where
  sub x y := { name := x.name - y.name, semitones := x.semitones - y.semitones }
instance : SMul Int Interval where
  smul n x := { name := n * x.name, semitones := n * x.semitones }

example : toString ma2 = "M2" := rfl
example : (toString p4) = "P4" := rfl
example : (toString p5) = "P5" := rfl
example : toString (p5 + Accidental.sharp) = "P5♯" := rfl

def majorTriad (p : Pitch) : List Pitch := [
    p, p + ma3, p + p5
  ]
def minorTriad (p : Pitch) : List Pitch := [
    p, p + mi3, p + p5
  ]

end Interval

/-- 7-tone diatonic scale -/
instance diatonic (root : Tone) (modus : Hep) : Scale Pitch Interval where
  name := s!"{root} {modus.modus}"
  fundamental := Interval.octave
  pitches := List.finRange 7 |>.map λ i =>
    let name := i.add root.name
    -- Nominal shift if the letters are read directly with the same accidentals
    let shiftNominal := (root.name : Fin 7).toNat.repeat List.rotateLeft spaces
      |>.take i.toNat |>.sum
    -- Actual shift determined by modus
    let shiftModus := (modus : Fin 7).toNat.repeat List.rotateLeft spaces
      |>.take i.toNat |>.sum
    { name, acc := ⟨shiftModus - shiftNominal + root.acc.semitones⟩ }

instance equalTempTuning root modus : Tuning Pitch EqualTemp.Pitch (src := (diatonic root modus).toPseudoScale) (dst := EqualTemp.et12.toPseudoScale) where
  liftPitch pitch :=
    -- Nominal shift if the letters are read directly with the same accidentals
    let shiftNominal := (root.name : Fin 7).toNat.repeat List.rotateLeft spaces
      |>.take pitch.hep.toNat |>.sum
    let total := shiftNominal + pitch.acc.semitones + pitch.octave * 12
    total

example : (Pitch.new .c 4) + Interval.octave = (Pitch.new .c 5) := rfl
example : (Pitch.new .c 4) + Interval.p5 = (Pitch.new .g 4) := rfl
example : (Pitch.new .b 5) + Interval.p5 = (Pitch.new .f 6 .sharp) := rfl
example : (Pitch.new .e 3) - (Pitch.new .c 3) = Interval.ma3 := rfl

abbrev Note [S : Time MeasuredTime Rat] := @Prismriver.Note Pitch MeasuredTime Rat S

structure Bar [S : Time MeasuredTime Rat] where
  noteValues : List Note
  timeTop: Nat
  timeBot : Nat
  deriving Inhabited

def time22 := timeSignature 2 2
def time44 := timeSignature 4 4
