import Prismriver.Repr.Scale
import Prismriver.Repr.Note
import Prismriver.Repr.Classical
import Lean.ToExpr

namespace Prismriver.Dihedral

open Classical
open Lean

inductive TransposeAction (P I) where
  /-- p → p + i -/
  | r (i : I)
  /-- p → a - (p - a) - I -/
  | sr (a : P) (i : I)

def rInterval (i : Interval) (p : Pitch) : Pitch :=
 let a : Pitch := p + i
 a

def srInterval (i : Interval) (a : Pitch) (p : Pitch) : Pitch :=
  let b : Pitch := a - (p - a) - i
  b

instance : SMul (TransposeAction Pitch Interval) Pitch where
  smul t p := match t with
    | .r i => rInterval i p
    | .sr a i => srInterval i a p

theorem add_Interval (i j : Interval) : i.name + j.name = (i + j).name := by
  unfold Interval.name
  rfl

theorem add_Semitones (i j : Interval) : i.semitones + j.semitones = (i + j).semitones := by
  unfold Interval.semitones
  rfl

theorem add_Interval_Pitch (i j : Interval) (p : Pitch) : p + j + i = p + (i + j) := by
  rw [← pitch_interval_add_comm]
  rw [pitch_interval_add_assoc]

theorem rInterval_rInterval (i j : Interval) (p : Pitch) : rInterval i (rInterval j p) = rInterval (i + j) p := by
  unfold rInterval
  simp
  rw [← pitch_interval_add_comm]
  rw [pitch_interval_add_assoc]

theorem rInterval_srInterval (i j : Interval) (a : Pitch) (p : Pitch) : rInterval i (srInterval j a p) = srInterval (j - i) a p := by
  unfold rInterval
  unfold srInterval
  simp
  have h1 : - (j - i) = -j + i := by
    rw [Interval.neg_neg_sub]
  have h2 : a - (p - a) - j + i = a - (p - a) + -j + i := by rfl
  rw [h2]
  rw [pitch_interval_add_assoc (-j) i (a - (p - a))]
  have h3 : a - (p - a) - (j - i) = a - (p - a) + -(j-i) := by rfl
  rw [h3]
  rw [h1]

theorem hSub_hAdd_Pitch (p a : Pitch) (j : Interval) : (p + j) - a = (p - a) +j := by
  apply Interval.ext
  unfold HAdd.hAdd instHAddPitchInterval
  unfold HSub.hSub instHSubPitchOutParamInterval
  simp
  unfold instHAdd
  unfold Add.add
  unfold Interval.instAdd
  simp
  omega
  unfold HAdd.hAdd instHAddPitchInterval
  unfold HSub.hSub instHSubPitchOutParamInterval
  simp
  unfold instHSub instHAdd
  simp
  unfold Add.add Sub.sub Interval.instAdd Accidental.instSub
  simp
  unfold Int.instSub Int.sub
  simp
  rw [nameDistance_swap (p.name + j.name) p.name]
  simp
  rw [Int.add_comm]
  rw [← nameDistance_image p.name (p.name + j.name) a.name]
  omega

theorem hSub_Interval_sum (p : Pitch) (i j : Interval) : p - (i + j) = p - i - j := by
  apply Pitch.ext
  unfold HAdd.hAdd instHAdd
  unfold HSub.hSub instHSubPitchInterval
  simp
  unfold Add.add Interval.instAdd
  simp
  omega
  unfold HAdd.hAdd instHAdd
  unfold HSub.hSub instHSubPitchInterval
  unfold Add.add Interval.instAdd
  simp
  have h1 : p.name + -(i.name + j.name) = p.name + -i.name + -j.name := by
    omega
  rw [h1]
  rw [← nameDistance_image (p.name + -i.name + -j.name) (p.name + -i.name) p.name]
  omega

theorem srInterval_rInterval (i j : Interval) (a p : Pitch) :
    srInterval i a (rInterval j p) = srInterval (i + j) a p := by
  unfold srInterval rInterval
  simp
  apply Pitch.ext
  rw [hSub_hAdd_Pitch p a j]
  rw [hSub_Interval_sum a (p - a) j]
  have : a - (p - a) - j - i = a - (p - a) + -j + -i := by rfl
  rw [this]
  rw [Interval.add_comm]
  rw [hSub_Interval_sum]
  have h1 : (a - (p - a) - j - i).name = (a - (p - a) + -j + -i).name := by rfl
  rw [h1]
  rw [hSub_Interval_sum]
  have h1 : (a - (p - a) - i - j).acc = (a - (p - a) + -i + -j).acc := by rfl
  rw [h1]
  rw [hSub_hAdd_Pitch p a j]
  rw [hSub_Interval_sum a (p - a) j]
  have h2 :  (a - (p - a) - j - i).acc = (a - (p-a) + -j + -i).acc := by rfl
  rw [h2]
  rw [pitch_interval_add_comm]

theorem sub_Pitch_Interval_acc (p : Pitch) (i : Interval) :
    (p - i).acc = { semitones := p.acc.semitones - i.semitones - nameDistance (p.name + -i.name) p.name } := rfl

theorem add_Pitch_Interval_acc (p : Pitch) (i : Interval) :
    (p + i).acc = { semitones := p.acc.semitones + i.semitones - nameDistance (p.name + i.name) p.name }
  := rfl

theorem sub_Pitch_Pitch_semitones (p q : Pitch) :
    (p - q).semitones = nameDistance p.name q.name + (p.acc - q.acc).semitones := rfl

theorem sub_Pitch_Interval_name (p : Pitch) (i : Interval) :
    (p - i).name = p.name + -i.name := rfl

theorem add_Pitch_Interval_name (p : Pitch) (i : Interval) :
    (p + i).name = p.name + i.name := rfl

theorem sub_Pitch_Pitch_name (p q : Pitch) :
    (p - q).name = p.name - q.name := rfl

theorem sub_Accidental_semitones (x y : Accidental) :
    (x - y).semitones = x.semitones - y.semitones := rfl

theorem srInterval_srInterval (i j : Interval) (p a : Pitch) : srInterval i a (srInterval j a p) = rInterval (j - i) p := by
  unfold srInterval
  unfold rInterval
  simp
  have h1 : a - (a - (p - a) - j - a) = p + j := by
    apply Pitch.ext
    unfold HSub.hSub instHSubPitchInterval instHSubPitchOutParamInterval
    simp
    have a : (p.name - a.name) = (p.name + -a.name) := by rfl
    rw [a]
    rw [Int.add_assoc]
    have b : (p + j).name = p.name + j.name := by rfl
    rw [b]
    omega
    apply Accidental.ext
    simp only [sub_Pitch_Interval_acc, add_Pitch_Interval_acc,
                 sub_Pitch_Interval_name, sub_Pitch_Pitch_name, sub_Pitch_Pitch_semitones,
                 sub_Accidental_semitones]
    have hI1 := nameDistance_image (a.name + -(p.name - a.name) + -j.name)
                                  (a.name + -(p.name - a.name))
                                  a.name
    have hI2 := nameDistance_image (p.name + j.name) p.name a.name
    grind
  rw [h1]
  have h2 : p + j - i = p + j + -i := by rfl
  rw [h2]
  rw [pitch_interval_add_assoc]
  rfl

theorem pitch_sub_pitch_sub_self (a b : Pitch) : a - (a - b) = b := by
  apply Pitch.ext
  simp only [sub_Pitch_Interval_name, sub_Pitch_Pitch_name]
  omega
  apply Accidental.ext
  simp only [sub_Pitch_Interval_acc, sub_Pitch_Pitch_name, sub_Pitch_Pitch_semitones, sub_Accidental_semitones]
  have hname : a.name + -(a.name - b.name) = b.name := by omega
  rw [hname]
  rw [nameDistance_swap b.name a.name]
  omega

theorem pitch_sub_add_pitch_sub (a b p : Pitch) : (a - b) + (p - a) = p - b := by
  apply Interval.ext
  unfold HAdd.hAdd instHAdd Add.add Interval.instAdd
  simp only [sub_Pitch_Pitch_name]
  omega
  unfold HAdd.hAdd instHAdd Add.add Interval.instAdd
  simp only [sub_Pitch_Pitch_semitones, sub_Accidental_semitones]
  rw [← nameDistance_image p.name a.name b.name]
  omega

theorem srInterval_change_center
    (j : Interval) (a b p : Pitch) :
    srInterval j b p = srInterval ((a - b) + (a - b) + j) a p := by
    apply Pitch.ext
    unfold srInterval
    simp only [HSub.hSub, Neg.neg, HAdd.hAdd, Add.add]
    grind
    unfold srInterval
    simp
    rw [hSub_Interval_sum (a - (p - a)) ((a - b) + (a - b)) j]
    have : (a - (p - a) - (a - b + (a - b)) - j).acc = (a - (p - a) - (a - b + (a - b)) - j).acc := by grind
    rw [this]
    rw [pitch_interval_sub_comm a (p - a) (a - b + (a-b))]
    rw [hSub_Interval_sum a (a - b) (a - b)]
    rw [pitch_sub_pitch_sub_self a b]
    rw [pitch_interval_sub_comm b (a - b) (p - a)]
    rw [← hSub_Interval_sum b (p - a) (a - b)]
    have : (b - (p - a + (a - b)) - j).acc = (b - (p - b) - j).acc := by
      rw [Interval.add_comm (p - a) (a - b)]
      rw [pitch_sub_add_pitch_sub a b p]
    rw [this]

theorem srInterval_srInterval_general (i j : Interval) (a b p : Pitch) :
  srInterval i a (srInterval j b p) = rInterval ((a - b) + (a - b) + (j - i)) p := by
  rw [srInterval_change_center j a b p]
  rw [srInterval_srInterval]
  unfold rInterval
  simp
  unfold HAdd.hAdd instHAddPitchInterval instHAdd Add.add Interval.instAdd
  simp
  unfold HSub.hSub instHSubPitchOutParamInterval instHSub Sub.sub Interval.instSub
  simp
  grind

instance : Mul (TransposeAction Pitch Interval) where
  mul
  | .r i, .r j => .r (i + j)
  | .r i, .sr a j => .sr a (j - i)
  | .sr a i, .r j => .sr a (i + j)
  | .sr a i, .sr b j => .r ((a - b) + (a - b) + (j - i))

theorem transposeAction_mul_smul (t1 t2 : TransposeAction Pitch Interval) (p : Pitch) :
  t1 • (t2 • p) = (t1 * t2) • p := by
  cases t1 <;> cases t2 <;> simp [HMul.hMul, Mul.mul]
  unfold HSMul.hSMul instHSMul SMul.smul instSMulTransposeActionPitchInterval
  simp
  rw [rInterval_rInterval]
  unfold HSMul.hSMul instHSMul SMul.smul instSMulTransposeActionPitchInterval
  simp
  rw [rInterval_srInterval]
  unfold HSMul.hSMul instHSMul SMul.smul instSMulTransposeActionPitchInterval
  simp
  rw [srInterval_rInterval]
  unfold HSMul.hSMul instHSMul SMul.smul instSMulTransposeActionPitchInterval
  simp
  rename_i j
  rename_i b
  rename_i i
  rename_i a
  rw [srInterval_srInterval_general]
