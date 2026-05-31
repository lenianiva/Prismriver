import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Prismriver.Repr.Classical
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Prismriver.Repr.Dihedral
namespace Prismriver.Theory.Dihedral

open Classical
open Lean
open Dihedral

inductive Parity : Type | major | minor
deriving DecidableEq, Repr, Fintype

instance : ToString Parity where
  toString | .major => "major" | .minor => "minor"

def Parity.flip : Parity → Parity
  | .major => .minor
  | .minor => .major

abbrev Triad := ZMod 12 × Parity

def pitch_toZMod12 (p : Pitch) : ZMod 12 :=
  (p.acc.semitones + nameDistance p.name 0 : Int)

def interval_toZMod12 (i : Interval) : ZMod 12 :=
  (i.semitones : ZMod 12)

def ZMod12ToPitch : ZMod 12 → Pitch
  | 0 => Pitch.new .c 0
  | 1 => Pitch.new .c 0 .sharp
  | 2 => Pitch.new .d 0
  | 3 => Pitch.new .d 0 .sharp
  | 4 => Pitch.new .e 0
  | 5 => Pitch.new .f 0
  | 6 => Pitch.new .f 0 .sharp
  | 7 => Pitch.new .g 0
  | 8 => Pitch.new .g 0 .sharp
  | 9 => Pitch.new .a 0
  | 10 => Pitch.new .a 0 .sharp
  | 11 => Pitch.new .b 0

instance : ToString Triad where
  toString t :=
    let pitch := ZMod12ToPitch t.1
    s!"({pitch}, {t.2})"

def TransposeAction.toDihedral :
      @TransposeAction Pitch Interval → DihedralGroup 12
    | .r i =>
        DihedralGroup.r (interval_toZMod12 i)
    | .sr a i =>
        DihedralGroup.sr (interval_toZMod12 i - 2 * pitch_toZMod12 a)

-- convert triad to list of pitches
def recoverTriple (t : Triad) : List Pitch :=
  match t.2 with
  | .major => majorTriad (ZMod12ToPitch t.1)
  | .minor => minorTriad (ZMod12ToPitch (t.1 + 5))

def transposeTriad (n : ZMod 12) (t : Triad) : Triad :=
  (t.1 + n, t.2)

def invertTriad (n : ZMod 12) (t : Triad) : Triad :=
    (-t.1 + n, t.2.flip)

-- note: mathlib's dihedral group uses the opposite rotation convention from the paper.
-- The paper's T_n corresponds to Mathlib's r (-n), not r n.
-- paper's s^12=1, t^2=1, tst=s^{-1} vs Mathlib's r * sr = sr (j - i).
-- fix is transposing by -n when the group element is r n.
instance : SMul (DihedralGroup 12) Triad where
  smul g t :=
    match g with
    | DihedralGroup.r n =>
        transposeTriad n t
    | DihedralGroup.sr n =>
        invertTriad (-n) t

lemma transposeTriad_zero (t : Triad) :
    transposeTriad 0 t = t := by
    unfold transposeTriad
    simp

-- Tm ◦ Tn = Tm+n mod 12
lemma transposeTriad_add (i j : ZMod 12) (t : Triad) :
    transposeTriad i (transposeTriad j t) = transposeTriad (i + j) t := by
    unfold transposeTriad
    simp
    rw [add_assoc]
    simp
    rw [add_comm]

-- for all pitch action, there exists dihedral such that action applied to pitch = dihedral applied to pitch
-- = dihedralize a acts on equivalence class of pitch
-- image of an operation

-- Tm ◦ In = Im+n mod 12
lemma transposeInverse_add (i j : ZMod 12) (t : Triad) :
  transposeTriad i (invertTriad j t) = invertTriad (i + j) t := by
  unfold invertTriad
  unfold transposeTriad
  simp
  rw [add_assoc]
  simp
  rw [add_comm]

-- Im ◦ Tn = Im−n mod 12
lemma inverseTranspose_subtract (i j : ZMod 12) (t : Triad) :
  invertTriad i (transposeTriad j t) = invertTriad (i - j) t := by
  unfold invertTriad
  unfold transposeTriad
  simp
  rw [sub_eq_add_neg]
  rw [add_assoc]
  rw [add_comm]
  rw [add_assoc]

-- Im ◦ In = Tm−n mod 12
lemma inverseInverse_subtract (i j : ZMod 12) (t : Triad) :
  invertTriad i (invertTriad j t) = transposeTriad (i - j) t := by
  unfold invertTriad
  unfold transposeTriad
  simp
  rw [sub_eq_add_neg]
  constructor
  rw [add_assoc]
  rw [add_comm]
  rw [add_assoc]
  cases t.2
  rfl
  rfl

lemma inverseInverse_subtract' (i j : ZMod 12) (t : Triad) :
  invertTriad (-i) (invertTriad (-j) t) = transposeTriad (j - i) t := by
  unfold invertTriad
  unfold transposeTriad
  simp
  rw [sub_eq_add_neg]
  constructor
  rw [add_assoc]
  rw [add_comm]
  rw [add_assoc]
  simp
  rw [add_comm]
  cases t.2
  rfl
  rfl

instance : MulAction (DihedralGroup 12) Triad where
    one_smul t := by
      cases t
      simp only [DihedralGroup.one_def]
      apply transposeTriad_zero
    mul_smul t x y := by
      cases t <;> cases x
      · -- r.r
        rw [DihedralGroup.r_mul_r]
        simp only [HSMul.hSMul, SMul.smul]
        symm
        apply transposeTriad_add
      · -- r.sr
        rw [DihedralGroup.r_mul_sr]
        simp only [HSMul.hSMul, SMul.smul]
        simp only [sub_eq_add_neg, neg_add_rev, neg_neg]
        symm
        apply transposeInverse_add
      · -- sr.r
        rw [DihedralGroup.sr_mul_r]
        simp only [HSMul.hSMul, SMul.smul]
        symm
        rw [neg_add']
        apply inverseTranspose_subtract
      · -- sr.sr
        rw [DihedralGroup.sr_mul_sr]
        simp only [HSMul.hSMul, SMul.smul]
        symm
        apply inverseInverse_subtract'

local instance : Scale Pitch Interval := diatonic ⟨.c, .natural⟩ .c

lemma pitch_toZMod12_smul_interval (p : Pitch) (i : Interval) :
  pitch_toZMod12 (i • p) = pitch_toZMod12 p + interval_toZMod12 i := by
  unfold pitch_toZMod12 interval_toZMod12
  simp only [smul_Pitch_Interval_acc, smul_Pitch_Interval_name]
  rw [← nameDistance_image (p.name + i.name) p.name 0]
  grind

lemma pitch_toZMod12_smul_neg_interval (p : Pitch) (i : Interval) :
    pitch_toZMod12 ((-i) • p) =
      pitch_toZMod12 p - interval_toZMod12 i := by
  rw [pitch_toZMod12_smul_interval]
  unfold pitch_toZMod12 interval_toZMod12
  simp only [Interval.instNeg]
  grind

lemma interval_toZMod12_pitch_sub_pitch (p q : Pitch) :
    interval_toZMod12 (p / q) =
      pitch_toZMod12 p - pitch_toZMod12 q := by
  unfold pitch_toZMod12 interval_toZMod12
  simp only [div_Pitch_Pitch_semitones, Accidental.sub_Accidental_semitones]
  rw [← nameDistance_image p.name q.name 0]
  grind

lemma pitch_toZMod12_srInterval (a p : Pitch) (i : Interval) :
    pitch_toZMod12 (srInterval i a p) = 2 * pitch_toZMod12 a - pitch_toZMod12 p - interval_toZMod12 i := by
  unfold srInterval
  have h1 : (-(p / a) - i) = -((p / a) + i) := by
    apply Interval.ext
    unfold HSub.hSub instHSub Sub.sub Interval.instSub
    unfold HAdd.hAdd instHAdd Add.add Interval.instAdd
    unfold Neg.neg Interval.instNeg
    grind
    unfold HSub.hSub instHSub Sub.sub Interval.instSub
    unfold HAdd.hAdd instHAdd Add.add Interval.instAdd
    unfold Neg.neg Interval.instNeg
    grind
  rw [h1]
  rw [pitch_toZMod12_smul_neg_interval a ((p / a) + i)]
  have h2 : interval_toZMod12 ((p / a) + i) = interval_toZMod12 (p / a) + interval_toZMod12 i := by
    unfold interval_toZMod12
    unfold HAdd.hAdd instHAdd Add.add Interval.instAdd
    simp
    rfl
  rw [h2]
  rw [interval_toZMod12_pitch_sub_pitch]
  rw [two_mul]
  grind

def pitchTriad (p : Pitch) (q : Parity) : Triad := (pitch_toZMod12 p, q)

def TransposeAction.mapParity : @TransposeAction Pitch Interval → Parity → Parity
  | .r _, q => q
  | .sr _ _, q => q.flip

theorem transposeAction_toDihedral_triad (t : @TransposeAction Pitch Interval) (p : Pitch) (q : Parity) :
  TransposeAction.toDihedral t • pitchTriad p q = pitchTriad (t • p) (TransposeAction.mapParity t q) := by
  cases t
  apply Prod.ext
  unfold pitchTriad TransposeAction.toDihedral HSMul.hSMul instHSMul SMul.smul instSMulDihedralGroupOfNatNatTriad
  simp
  unfold transposeTriad instSMulTransposeAction rInterval
  simp
  rw [pitch_toZMod12_smul_interval]
  unfold pitchTriad TransposeAction.toDihedral TransposeAction.mapParity
  unfold HSMul.hSMul instHSMul SMul.smul instSMulDihedralGroupOfNatNatTriad transposeTriad
  simp
  apply Prod.ext
  unfold pitchTriad TransposeAction.toDihedral HSMul.hSMul instHSMul SMul.smul instSMulDihedralGroupOfNatNatTriad
  simp
  unfold invertTriad instSMulTransposeAction
  simp
  rw [add_comm]
  rename_i a
  rename_i i
  have : 2 * pitch_toZMod12 i - interval_toZMod12 a + -pitch_toZMod12 p = 2 * pitch_toZMod12 i - pitch_toZMod12 p - interval_toZMod12 a := by
    unfold pitch_toZMod12
    unfold interval_toZMod12
    grind
  rw [this]
  symm
  rw [pitch_toZMod12_srInterval]
  unfold pitchTriad TransposeAction.toDihedral TransposeAction.mapParity
  unfold HSMul.hSMul instHSMul SMul.smul instSMulDihedralGroupOfNatNatTriad invertTriad
  simp
