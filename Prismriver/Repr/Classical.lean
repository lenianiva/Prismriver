import Prismriver.Repr.Scale
import Prismriver.Repr.Note

namespace Prismriver.Classical

/-- Accidental measured in terms of the number of semitones from natural. -/
@[ext]
structure Accidental where
  semitones : Int := 0
  deriving BEq, Inhabited, Ord

instance : LT Accidental := ltOfOrd
instance : LE Accidental := leOfOrd

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
instance : Neg Accidental where
  neg x := { semitones := -x.semitones }
instance : Sub Accidental where
  sub x y := { semitones := x.semitones - y.semitones }
instance : HMul Int Accidental Accidental where
  hMul n x := { semitones := n * x.semitones }

theorem add_comm (i j : Accidental) : i + j = j + i := by
  unfold HAdd.hAdd instHAdd Accidental.instAdd
  simp
  apply Int.add_comm

theorem add_assoc (i j k : Accidental) : (i + j) + k = i + (j + k) := by
  unfold HAdd.hAdd instHAdd Accidental.instAdd
  simp
  apply Int.add_assoc

theorem sub_neg (i j : Accidental) : i - (-j) = i + j := by
  unfold HAdd.hAdd instHAdd Accidental.instAdd
  unfold HSub.hSub instHSub Accidental.instSub
  simp
  apply Int.sub_neg

theorem add_mul (n m : Int) (i : Accidental) : (n + m) * i = n * i + m * i := by
  unfold HAdd.hAdd instHAdd Accidental.instAdd
  unfold HMul.hMul Accidental.instHMulInt
  simp
  apply Int.add_mul

theorem sub_Accidental_semitones (x y : Accidental) :
    (x - y).semitones = x.semitones - y.semitones := rfl

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

/-- Equivalence classes of pitches modulo octave -/
@[ext]
structure Tone where
  name : Hep
  acc : Accidental := .natural
  deriving BEq, Inhabited

instance : ToString Tone where
  toString t := if t.acc == .natural then toString t.name else s!"{t.name}{t.acc}"

@[ext]
structure Pitch where
  name : Int
  acc : Accidental := .natural
  deriving BEq, Inhabited, Ord

instance : LT Pitch := ltOfOrd
instance : LE Pitch := leOfOrd

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

example : Pitch.c4 < (⟨7 * 4, .sharp⟩ : Pitch) := by decide

end Pitch

private def nameDistanceAux (total : Nat) (key : Fin 7) : Nat → Nat
  | 0 => total
  | remainder+1 =>
    nameDistanceAux (total + spaces[key]) (key + (1 : Fin 7)) remainder

private theorem nameDistanceAux_total (t1 t2 : Nat) (key : Fin 7) (a : Nat)
  : t1 + (nameDistanceAux t2 key a) = nameDistanceAux (t1 + t2) key a := by
  induction a generalizing t1 t2 key
  case zero =>
    rfl
  unfold nameDistanceAux
  rename_i this
  simp
  rewrite [this]
  rewrite [Nat.add_assoc]
  rfl

private theorem nameDistanceAux_next (total : Nat) (key : Fin 7) (n : Nat)
  : nameDistanceAux total key (n + 1) = (nameDistanceAux total (key + 1) n) + spaces[key]
  := by
  unfold nameDistanceAux
  split
  . unfold nameDistanceAux
    rfl
  conv =>
    lhs
    unfold nameDistanceAux
  conv =>
    rhs
    apply Nat.add_comm
  rewrite [nameDistanceAux_total spaces[key]]
  congr 1
  omega

private theorem nameDistanceAux_image (total : Nat) (key : Fin 7) (n m : Nat)
  : nameDistanceAux total key (n + m) = nameDistanceAux 0 key n + nameDistanceAux total (key + (Fin.ofNat 7 n)) m := by
  induction n generalizing total key m
  case zero =>
    simp
    unfold nameDistanceAux
    simp
  case succ n hi =>
    rewrite [Nat.add_comm, ← Nat.add_assoc]
    repeat rewrite [nameDistanceAux_next]
    rewrite [Nat.add_comm m _]
    rw [Fin.add_ofNat]
    rw [hi]
    rw [Fin.add_ofNat]
    simp
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    congr 1
    refine Eq.symm (Fin.eq_of_val_eq ?_)
    simp
    refine Nat.add_mod_eq_add_mod_left n ?_
    grind

private theorem nameDistanceAux_sub_eq_addNeg (total : Nat) (key : Fin 7) (n m : Int)
  : nameDistanceAux total key (n - m).toNat = nameDistanceAux total key ((n + -(m)).toNat) := by
  induction n generalizing total key m
  case ofNat =>
    simp
    rfl
  case negSucc =>
    rfl

/-- Calculates the semitone distance of `n2 - n1` two pitches with no accidentals -/
def nameDistance (n2 n1 : Int) : Int :=
  if n1 ≤ n2 then
    let fin : Fin 7 := Fin.intCast n1
    nameDistanceAux 0 fin (Int.toNat (n2 - n1))
  else
    let fin : Fin 7 := Fin.intCast n2
    let d : Int := nameDistanceAux 0 fin (Int.toNat (n1 - n2))
    (-d : Int)

theorem nameDistance_refl (i : Int) : nameDistance i i = 0 := by
  unfold nameDistance
  split
  simp
  rfl
  simp
  rfl

theorem nameDistance_swap (i j : Int) : nameDistance i j = - (nameDistance j i) := by
  unfold nameDistance
  repeat split <;> split
  . have : i = j := Int.le_antisymm ‹i ≤ j› ‹j ≤ i›
    rw [Int.sub_eq_zero.mpr this]
    have : j = i := Eq.symm this
    rw [Int.sub_eq_zero.mpr this]
    rw [this]
    rfl
  . simp
  . simp
  . have : j < i := Int.lt_of_not_ge ‹¬ i ≤ j›
    have : j ≤ i := Int.le_of_lt this
    contradiction

private theorem intCast_key (a b : Int) (h : b ≤ a) :
    Fin.intCast b + Fin.ofNat 7 ((a + -b).toNat) = (Fin.intCast a : Fin 7) := by grind [Fin.intCast]

theorem nameDistance_image (i j k : Int) : nameDistance i j + nameDistance j k = nameDistance i k := by
  unfold nameDistance
  simp
  split
  split
  . have : k ≤ i := Int.le_trans ‹k ≤ j› ‹j ≤ i›
    rewrite [if_pos this]
    repeat rewrite [nameDistanceAux_sub_eq_addNeg]
    symm
    have hsplit : (i + -k).toNat = (j + -k).toNat + (i + -j).toNat := by omega
    rw [hsplit, nameDistanceAux_image]
    simp
    rw [Int.add_comm]
    simp
    congr 1
    rw [intCast_key j k ‹k ≤ j›]
  . split
    repeat rewrite [nameDistanceAux_sub_eq_addNeg]
    have hsplit : (i + -j).toNat = (k + -j).toNat + (i + -k).toNat := by omega
    symm
    rw [hsplit, nameDistanceAux_image]
    simp
    rw [Int.add_comm]
    congr 1
    rw [← intCast_key k j (by omega)]
    omega
    rw [nameDistanceAux_sub_eq_addNeg, nameDistanceAux_sub_eq_addNeg, nameDistanceAux_sub_eq_addNeg]
    symm
    have hsplit : (k + -j).toNat = (i + -j).toNat + (k + -i).toNat := by omega
    rw [hsplit, nameDistanceAux_image]
    rw [← intCast_key i j ‹j ≤ i›]
    omega
  rw [nameDistanceAux_sub_eq_addNeg]
  rw [nameDistanceAux_sub_eq_addNeg]
  rw [nameDistanceAux_sub_eq_addNeg]
  split
  split
  rw [nameDistanceAux_sub_eq_addNeg]
  symm
  have hsplit : (j + -k).toNat = (i + -k).toNat + (j + -i).toNat := by omega
  rw [hsplit, nameDistanceAux_image]
  rw [← intCast_key i k ‹k ≤ i›]
  simp
  omega
  rw [nameDistanceAux_sub_eq_addNeg]
  have hsplit : (j + -i).toNat = (k + -i).toNat + (j + -k).toNat := by omega
  rw [hsplit, nameDistanceAux_image]
  rw [← intCast_key k i (by omega)]
  omega
  split
  omega
  rw [nameDistanceAux_sub_eq_addNeg]
  have hsplit : (k + -i).toNat = (j + -i).toNat + (k + -j).toNat := by omega
  rw [hsplit, nameDistanceAux_image]
  rw [← intCast_key j i (by omega)]
  grind

/-- An interval consists of a letter distance and a semitone distance -/
@[ext]
structure Interval where
  name : Int
  semitones : Int
  deriving BEq, Inhabited

namespace Interval

@[simp, reducible]
protected def zero : Interval := ⟨0, 0⟩

instance : Add Interval where
  add x y := { name := x.name + y.name, semitones := x.semitones + y.semitones }
instance : Sub Interval where
  sub x y := { name := x.name - y.name, semitones := x.semitones - y.semitones }
instance : HMul Int Interval Interval where
  hMul n x := { name := n * x.name, semitones := n * x.semitones }
instance : HMul Nat Interval Interval where
  hMul n x := (n : Int) * x

theorem add_name (i j : Interval) : i.name + j.name = (i + j).name := by
  unfold Interval.name
  rfl

theorem add_semitones (i j : Interval) : i.semitones + j.semitones = (i + j).semitones := by
  unfold Interval.semitones
  rfl

instance : Neg Interval where
  neg i := { name := -i.name, semitones := -i.semitones }

theorem add_comm (x y : Interval) : x + y = y + x := by
  unfold HAdd.hAdd instHAdd Add.add instAdd
  simp
  constructor
  rw [Int.add_comm]
  rw [Int.add_comm]

theorem add_assoc (i j k: Interval) : (i + j) + k = i + (j + k) := by
  unfold HAdd.hAdd instHAdd Add.add instAdd
  simp
  constructor
  rw [Int.add_assoc]
  rw [Int.add_assoc]

theorem add_left_neg (i : Interval) : (-i) + i = Interval.zero := by
  unfold HAdd.hAdd instHAdd Add.add Interval.instAdd
  simp
  unfold Neg.neg Interval.instNeg
  simp
  constructor
  omega
  omega

theorem sub_neg (i j : Interval) : i - (-j) = i + j := by
  unfold HSub.hSub instHSub Sub.sub instSub
  apply Interval.ext
  simp
  unfold HAdd.hAdd instHAdd Add.add instAdd
  simp
  rw [Int.sub_eq_add_neg]
  simp
  unfold Neg.neg Int.instNegInt instNeg
  simp
  grind
  simp
  rw [Int.sub_eq_add_neg]
  have : i.semitones + -(-j).semitones = (i + -(-j)).semitones := by rfl
  rw [this]
  unfold Neg.neg instNeg
  simp

theorem neg_neg_sub (i j : Interval) : - (j - i) = -j + i := by
  have : j - i = j + -i := by
    unfold HSub.hSub instHSub Sub.sub instSub
    simp
    unfold HAdd.hAdd instHAdd Add.add instAdd
    simp
    constructor
    rw [Int.sub_eq_add_neg]
    rfl
    rfl
  rw [this]
  have : -(j + -i) = -j + i := by
    unfold HAdd.hAdd instHAdd Add.add instAdd
    simp
    unfold Neg.neg instNeg
    simp
    constructor
    omega
    omega
  rw [this]

theorem neg_add (i j: Interval) : - (j + i) = -j + -i := by
  unfold HAdd.hAdd instHAdd Add.add instAdd
  apply Interval.ext
  . unfold Neg.neg instNeg Int.instNegInt
    grind
  . unfold Neg.neg instNeg
    grind

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

example : toString ma2 = "M2" := rfl
example : (toString p4) = "P4" := rfl
example : (toString p5) = "P5" := rfl
example : toString (p5 + Accidental.sharp) = "P5♯" := rfl

end Interval

instance : HDiv Pitch Pitch (outParam Interval) where
  hDiv p1 p2 :=
    let Δname := nameDistance p1.name p2.name
    let Δacc := p1.acc - p2.acc
    { name := p1.name - p2.name, semitones := Δname + Δacc.semitones }

/-- Group action of interval group on the set of pitches -/
instance : HSMul Interval Pitch Pitch where
  hSMul i p :=
    let name := p.name + i.name
    -- Semitones accounted for in the name with no accidentals
    let Δsemitones := nameDistance name p.name
--    { name, acc := { semitones := i.semitones - Δsemitones} }
   { name, acc := { semitones := (p.acc.semitones + i.semitones) - Δsemitones} }

open Interval in
def majorTriad (p : Pitch) : List Pitch := [
    p, ma3 • p, p5 • p
  ]
open Interval in
def minorTriad (p : Pitch) : List Pitch := [
    p, mi3 • p, p5 • p
  ]
example : Interval.octave • (Pitch.new .c 4) = (Pitch.new .c 5) := rfl
example : Interval.p5 • (Pitch.new .c 4) = (Pitch.new .g 4) := rfl
example : Interval.p5 • (Pitch.new .b 5) = (Pitch.new .f 6 .sharp) := rfl
example : (Pitch.new .e 3) / (Pitch.new .c 3) = Interval.ma3 := rfl
example : (-Interval.p5) • (Interval.p5 • Pitch.new .c 4) = Pitch.new .c 4 := rfl
example : (-Interval.ma3) • (Interval.ma3 • Pitch.new .e 3) = Pitch.new .e 3 := rfl

theorem smul_Pitch_Interval_acc (p : Pitch) (i : Interval) :
    (i • p).acc = { semitones := p.acc.semitones + i.semitones - nameDistance (p.name + i.name) p.name }
  := rfl

theorem div_Pitch_Pitch_semitones (p q : Pitch) :
    (p / q).semitones = nameDistance p.name q.name + (p.acc - q.acc).semitones := rfl

theorem smul_Pitch_Interval_name (p : Pitch) (i : Interval) :
    (i • p).name = p.name + i.name := rfl

theorem div_Pitch_Pitch_name (p q : Pitch) :
    (p / q).name = p.name - q.name := rfl

theorem pitch_interval_add_comm (i j : Interval) (p : Pitch) : i • (j • p) = j • (i • p):= by
  unfold HSMul.hSMul instHSMulIntervalPitch
  simp only [Pitch.mk.injEq, Accidental.mk.injEq]
  constructor
  rw [Int.add_right_comm]
  have h1 : (p.name + i.name + j.name) = (p.name + j.name + i.name) := by omega
  rw [← h1]
  have hsI  := nameDistance_swap (p.name + i.name + j.name) (p.name + i.name)
  have hsI' := nameDistance_swap (p.name + i.name) p.name
  rw [hsI']
  simp
  rw [hsI]
  simp
  rw [nameDistance_swap (p.name + j.name) p.name]
  rw [nameDistance_swap (p.name + i.name + j.name) (p.name + j.name)]
  simp
  rw [Int.add_right_comm (p.acc.semitones + i.semitones + nameDistance p.name (p.name + i.name))
                     j.semitones
                     (nameDistance (p.name + i.name) (p.name + i.name + j.name))]
  rw [Int.add_assoc (p.acc.semitones + i.semitones)
                (nameDistance p.name (p.name + i.name))
                (nameDistance (p.name + i.name) (p.name + i.name + j.name))]
  rw [nameDistance_image p.name (p.name + i.name) (p.name + i.name + j.name)]
  rw [Int.add_comm (p.acc.semitones + i.semitones) (nameDistance p.name (p.name + i.name + j.name))]
  rw [Int.add_assoc (nameDistance p.name (p.name + i.name + j.name)) (p.acc.semitones + i.semitones) j.semitones]
  rw [Int.add_comm (p.acc.semitones + j.semitones) (nameDistance p.name (p.name + j.name))]
  rw [Int.add_assoc (nameDistance p.name (p.name + j.name)) (p.acc.semitones + j.semitones) i.semitones]
  rw [Int.add_comm (nameDistance p.name (p.name + j.name)) (p.acc.semitones + j.semitones + i.semitones)]
  rw [Int.add_assoc (p.acc.semitones + j.semitones + i.semitones) (nameDistance p.name (p.name + j.name)) (nameDistance (p.name + j.name) (p.name + i.name + j.name))]
  rw [nameDistance_image p.name (p.name + j.name) (p.name + i.name + j.name)]
  rw [Int.add_comm (nameDistance p.name (p.name + i.name + j.name)) (p.acc.semitones + i.semitones + j.semitones)]
  rw [Int.add_right_comm p.acc.semitones j.semitones i.semitones]

theorem pitch_interval_add_assoc (i j : Interval) (p : Pitch) : j • (i • p) = (i + j) • p := by
  unfold HSMul.hSMul instHSMulIntervalPitch
  unfold Interval.instAdd
  simp only [Pitch.mk.injEq, Accidental.mk.injEq]
  constructor
  . apply Int.add_assoc
  rw [nameDistance_swap, ←Interval.add_semitones]
  rw [nameDistance_swap (p.name + i.name + j.name) (p.name + i.name)]
  simp
  conv =>
    rhs
    rewrite [Int.sub_eq_add_neg]
    rewrite [← nameDistance_swap]
  conv =>
    lhs
    lhs
    rewrite [
      Int.add_assoc _ _ j.semitones,
      Int.add_comm _ j.semitones,
      ← Int.add_assoc _ j.semitones _,
    ]
    lhs
    rewrite [Int.add_assoc]
  conv =>
    lhs
    rewrite [Int.add_assoc]
  simp
  rw [nameDistance_image, ← Interval.add_name, Int.add_assoc]

/-- Interval with only a name distance in a particular key. Also known as a generic interval -/
structure KeyInterval (root modus : Hep) where
  name : Int

instance : HAdd Pitch (KeyInterval root modus) Pitch where
  hAdd p i :=
    let name := p.name + i.name
    -- If the modus and root are equal, there should not be any shift since there are no flats or sharps
    let distance := i.name.fmod 7 |>.toNat
    let s1 := p.name.toNat + modus.toNat + 7 - root.toNat
    let shiftModus : Int := List.rotateLeft spaces s1
      |>.take distance |>.sum
    let shiftNominal : Int := List.rotateLeft spaces p.name.toNat
      |>.take distance |>.sum
    let Δsemitones := shiftModus - shiftNominal
    { name, acc := { semitones := p.acc.semitones + Δsemitones } }
instance : Neg (KeyInterval root modus) where
  neg i := { name := -i.name }

example : (Pitch.new .c 4) + (⟨2⟩ : KeyInterval .c .c) = (Pitch.new .e 4) := rfl
example : (Pitch.new .c 4) + (⟨3⟩ : KeyInterval .c .c) = (Pitch.new .f 4) := rfl
example : (Pitch.new .c 4) + (⟨-1⟩ : KeyInterval .c .c) = (Pitch.new .b 3) := rfl
example : (Pitch.new .a 3) + (⟨1⟩ : KeyInterval .d .a) = (Pitch.new .b 3 .flat) := rfl
example : (Pitch.new .a 3) + (⟨8⟩ : KeyInterval .d .a) = (Pitch.new .b 4 .flat) := rfl
example : (Pitch.new .a 3) + (⟨9⟩ : KeyInterval .d .a) = (Pitch.new .c 5) := rfl
example : (Pitch.new .d 4) + (⟨5⟩ : KeyInterval .d .a) = (Pitch.new .b 4 .flat) := rfl
example : (Pitch.new .d 4) + (⟨4⟩ : KeyInterval .d .d) = (Pitch.new .a 4) := rfl

instance : Add (KeyInterval root modus) where
  add x y := { name := x.name + y.name }
instance : Sub (KeyInterval root modus) where
  sub x y := { name := x.name - y.name }
instance : SMul Int (KeyInterval root modus) where
  smul n x := { name := n * x.name }
instance : Neg (KeyInterval root modus) where
  neg i := { name := -i.name }
instance : ToString (KeyInterval root modus) where
  toString i :=
    if i.name % 7 == 0 then
      s!"{i.name / 7}"
    else
      s!"{modus}/{i.name}"

namespace KeyInterval

protected def zero { root modus : Hep } : KeyInterval root modus := ⟨0⟩
/-- Generic interval octave is the same in every key -/
protected def octave { root modus : Hep } : KeyInterval root modus := ⟨7⟩

theorem rotateLeft_add_length {α : Type} (l : List α) (n : Nat) : List.rotateLeft l (n + l.length) = List.rotateLeft l n := by
  unfold List.rotateLeft
  simp

theorem add_sub_cancel_middle (a b c : Nat) : a + b + c - b = a + c := by
   apply Eq.symm
   apply Nat.eq_sub_of_add_eq
   exact Nat.add_right_comm a c b

/-- A plain key interval where the `root` and `modus` are equal do not impart any accidental -/
theorem plain_no_accidental { root : Hep } (p : Pitch) (i : KeyInterval root root)
  : (p + i).acc = p.acc := by
  unfold HAdd.hAdd
  unfold instHAddPitchKeyInterval
  have h : spaces.length = 7 := rfl
  rw [← h]
  simp only [add_sub_cancel_middle]
  rw [rotateLeft_add_length]
  simp

end KeyInterval

def diatonicFifths (root : Tone) (modus : Hep) : Int :=
  let eqv := (root.name : Fin 7) - (modus : Fin 7)
  let baseline := match eqv with
    | 0 => 0
    | 1 => 2
    | 2 => 4
    | 3 => -1
    | 4 => 1
    | 5 => 3
    | 6 => 5
  baseline + root.acc.semitones * 12

@[default_instance]
instance : Torsor Pitch Interval where
  zero := Interval.zero
  add_zero := by
    unfold HAdd.hAdd instHAdd Add.add Interval.instAdd Interval.zero
    simp
  add_comm := Interval.add_comm
  add_left_neg := Interval.add_left_neg
  add_right_neg i := by
    rw [Interval.add_comm]
    apply Interval.add_left_neg
  add_assoc := Interval.add_assoc
  zero_mul _ := by
    unfold Interval.instHMulInt HMul.hMul
    apply Interval.ext
    . simp
      apply Int.zero_mul
    . simp
      apply Int.zero_mul
  neg_sub i j := by
    rw [Interval.neg_neg_sub]
    rw [Interval.add_comm]
    rfl
  sub_neg i j := by
    rw [Interval.sub_neg]
  sub_eq_add_neg i j := by
    apply Interval.ext
    rfl
    rfl
  neg_neg i := by
    apply Interval.ext
    unfold Neg.neg Interval.instNeg
    grind
    unfold Neg.neg Interval.instNeg
    grind
  neg_add i := by
    intro j
    rw [Interval.neg_add]
  neg_mul x _n := by
    unfold Interval.instHMulInt HMul.hMul
    simp
    apply Interval.ext
    . simp only [Neg.neg]
      exact Int.neg_mul _n x.name
    . simp only [Neg.neg]
      exact Int.neg_mul _n x.semitones
  mul_distrib := by
    unfold Interval.instHMulInt HMul.hMul
    intro n m i
    simp
    apply Interval.ext
    . unfold HAdd.hAdd instHAdd Add.add Int.instAdd Interval.instAdd
      simp
      apply Int.add_mul
    . unfold HAdd.hAdd instHAdd Add.add Int.instAdd Interval.instAdd
      simp
      apply Int.add_mul
  smul_zero _ := by
    unfold HSMul.hSMul instHSMulIntervalPitch Interval.zero
    simp
    apply Pitch.ext
    constructor
    simp
    rewrite [nameDistance_refl]
    apply Accidental.ext
    simp
  smul_assoc p i j := pitch_interval_add_assoc i j p
  smul_div p q := by
    unfold HDiv.hDiv instHDivPitchOutParamInterval
    unfold HSMul.hSMul instHSMulIntervalPitch
    simp
    apply Pitch.ext
    simp
    omega
    apply Accidental.ext
    simp
    rw [Int.add_comm]
    have h1 : p.name + (q.name - p.name) = q.name := by omega
    rw [h1]
    have h2 : nameDistance q.name p.name + (q.acc - p.acc).semitones + p.acc.semitones - nameDistance q.name p.name = (q.acc - p.acc).semitones + p.acc.semitones + nameDistance q.name p.name - nameDistance q.name p.name := by omega
    rw [h2]
    have h3 : (q.acc - p.acc).semitones = q.acc.semitones - p.acc.semitones := by rfl
    rw [h3]
    have h4 : q.acc.semitones - p.acc.semitones + p.acc.semitones = q.acc.semitones := by omega
    rw [h4]
    grind
  div_smul_self i p := by
   unfold HDiv.hDiv instHDivPitchOutParamInterval
   unfold HSMul.hSMul instHSMulIntervalPitch
   simp
   apply Interval.ext
   simp
   rw [Int.add_comm]
   rw [Int.add_sub_cancel]
   simp
   rw [Int.add_comm]
   rw [Accidental.sub_Accidental_semitones]
   grind

instance chromatic : Scale Pitch Interval where
  name := "chromatic"
  fundamental := Interval.octave

  pitches := [
    .new .c 0,
    .new .c 0 .sharp,
    .new .d 0,
    .new .d 0 .sharp,
    .new .e 0,
    .new .f 0,
    .new .f 0 .sharp,
    .new .g 0,
    .new .g 0 .sharp,
    .new .a 0,
    .new .a 0 .sharp,
    .new .b 0,
  ]

/-- 7-tone diatonic scale -/
instance diatonic (root : Tone) (modus : Hep) : Scale Pitch Interval where
  name := s!"{root} {modus.modus}"

  zero := Interval.zero
  fundamental := Interval.octave

  pitches := List.finRange 7 |>.map λ i =>
    let name := i.toNat + root.name.toNat
    -- Nominal shift if the letters are read directly with the same accidentals
    let shiftNominal := List.rotateLeft spaces root.name.toNat
      |>.take i.toNat |>.sum
    -- Actual shift determined by modus
    let shiftModus := List.rotateLeft spaces modus.toNat
      |>.take i.toNat |>.sum
    { name, acc := ⟨shiftModus - shiftNominal + root.acc.semitones⟩ }
  add_zero := Torsor.add_zero
  add_comm := Torsor.add_comm
  add_assoc := Torsor.add_assoc
  add_left_neg := Torsor.add_left_neg
  sub_neg := Torsor.sub_neg
  neg_neg := Torsor.neg_neg
  zero_mul := Torsor.zero_mul
  sub_eq_add_neg := Torsor.sub_eq_add_neg
  smul_div := Torsor.smul_div
  neg_add := Torsor.neg_add
  mul_distrib := Torsor.mul_distrib
  neg_mul := Torsor.neg_mul
  smul_zero := Torsor.smul_zero
  smul_assoc := Torsor.smul_assoc
  div_smul_self := Torsor.div_smul_self
  add_right_neg := Torsor.add_right_neg
  neg_sub := Torsor.neg_sub

/-- Equal temperament tuning of diatonic scales -/
instance equalTempTuning root modus : Tuning Pitch EqualTemp.Pitch
         (src := (diatonic root modus).toPseudoScale)
         (dst := EqualTemp.et12.toPseudoScale) where
  liftPitch pitch :=
    -- Nominal shift if the letters are read directly with the same accidentals
    let shiftNominal := List.rotateLeft spaces root.name.toNat
      |>.take pitch.hep.toNat |>.sum
    let total := shiftNominal + pitch.acc.semitones + pitch.octave * 12
    total

example : (diatonic ⟨.d, .natural⟩ .a).pitches = [.new .d 0, .new .e 0, .new .f 0, .new .g 0, .new .a 0, .new .b 0 .flat, .new .c 1] := rfl

abbrev Note := @Prismriver.Note Pitch MeasuredTime
