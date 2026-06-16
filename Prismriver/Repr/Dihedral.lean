import Prismriver.Repr.Scale
import Prismriver.Repr.Note
import Lean.ToExpr

namespace Prismriver

open Lean

variable { P I } [Scale P I]

inductive TransposeAction where
  /-- p → p + i -/
  | r (i : I)
  /-- p → a - (p - a) - I -/
  | sr (a : P) (i : I)

def rInterval (i : I) (p : P) : P := i • p

def srInterval (i : I) (a : P) (p : P) : P := (- (p / a) - i) • a

instance : SMul (@TransposeAction P I) P where
  smul t p := match t with
    | .r i => rInterval i p
    | .sr a i => srInterval i a p

theorem rInterval_rInterval (i j : I) (p : P) : rInterval i (rInterval j p) = rInterval (i + j) p := by
  unfold rInterval
  rw [← Torsor.add_comm]
  rw [Torsor.smul_assoc]

theorem rInterval_srInterval (i j : I) (a p : P) : rInterval i (srInterval j a p) = srInterval (j - i) a p := by
  unfold rInterval srInterval
  rw [Torsor.smul_assoc]
  congr
  have h1 :-(p / a) - (j - i) = -(p / a) + -j + i := by
    have : j - i = j + -i := by rw [Torsor.sub_eq_add_neg]
    rw [this]
    rw [Torsor.sub_eq_add_neg]
    rw [Torsor.neg_add]
    rw [Torsor.neg_neg]
    rw [Torsor.add_assoc]
  rw [h1]
  have h2 : -(p / a) - j + i = -(p / a) + -j + i := by rw [Torsor.sub_eq_add_neg]
  rw [h2]

theorem hSub_hAdd_Pitch (p a : P) (j : I) : (j • p) / a = (p / a) + j := by
  rw [← Torsor.smul_div (P := P) (I := I) (p := a) (q := p)]
  rw [Torsor.smul_assoc]
  rw [Torsor.div_smul_self]
  rw [Torsor.div_smul_self]

theorem srInterval_rInterval (i j : I) (a p : P) :
    srInterval i a (rInterval j p) = srInterval (i + j) a p := by
  unfold srInterval rInterval
  rw [hSub_hAdd_Pitch]
  have h1 : (-(p / a + j) - i) • a = (-(p / a) + -j + -i) • a  := by
    rw [Torsor.sub_eq_add_neg]
    rw [Torsor.neg_add]
  rw [h1]
  have h2 : (-(p / a) - (i + j)) • a = (-(p / a) + -i + -j) • a := by
    rw [Torsor.sub_eq_add_neg]
    rw [Torsor.neg_add]
    rw [Torsor.add_assoc]
  rw [h2]
  have h3 : -(p / a) + -j + -i = -(p / a) + -i + -j := by
    rw [Torsor.add_assoc (-(p / a)) (-j) (-i)]
    rw [Torsor.add_assoc (-(p / a)) (-i) (-j)]
    rw [Torsor.add_comm (-j) (-i)]
  rw [h3]

theorem srInterval_srInterval (i j : I) (p a : P) : srInterval i a (srInterval j a p) = rInterval (j - i) p := by
  unfold srInterval rInterval
  rw [Torsor.div_smul_self (-(p / a) - j) a]
  rw [Torsor.neg_sub]
  rw [Torsor.sub_eq_add_neg j (-(p / a))]
  rw [Torsor.neg_neg]
  have h : j + (p / a) + -i = (p / a) + (j - i) := by
    rw [Torsor.add_comm j (p/a)]
    rw [Torsor.add_assoc]
    rw [Torsor.sub_eq_add_neg j i]
  have h1 : (j + (p / a) - i) • a = ((p / a) + (j - i)) • a := by
    rw [Torsor.sub_eq_add_neg (j + (p / a)) i]
    rw [h]
  rw [h1]
  rw [← Torsor.smul_assoc]
  rw [Torsor.smul_div]

theorem pitch_sub_add_pitch_sub (a b p : P) : (a / b) + (p / a) = p / b := by
  symm
  rw [← hSub_hAdd_Pitch a b (p / a)]
  rw [Torsor.smul_div]

theorem srInterval_change_center
    (j : I) (a b p : P) :
    srInterval j b p = srInterval ((a / b) + (a / b) + j) a p := by
    unfold srInterval
    symm
    have h1 : (-(p / a) - (a / b + a / b + j)) • a = (-(p / a) + -(a / b) + -(a / b) + -j) • a := by
      rw [Torsor.sub_eq_add_neg]
      rw [Torsor.neg_add]
      rw [Torsor.neg_add (a / b) (a / b)]
      rw [← Torsor.add_assoc (-(p / a)) (-(a / b) + -(a / b)) (-j)]
      rw [← Torsor.add_assoc (-(p / a)) (-(a / b)) (-(a / b))]
    rw [h1]
    rw [← Torsor.smul_div (P := P) (I := I) (p := b) (q := a)]
    rw [Torsor.smul_assoc]
    rw [Torsor.smul_div]
    rw [Torsor.sub_eq_add_neg]
    rw [Torsor.add_assoc]
    have h2 : a / b + (-(p / a) + -(a / b) + -(a / b) + -j) = -(p / a) + -(a / b) + -j := by
      rw [Torsor.add_comm]
      rw [Torsor.add_assoc ((-(p / a) + -(a / b)) + -(a / b)) (-j) (a / b)]
      rw [Torsor.add_comm (-j) (a / b)]
      rw [Torsor.add_assoc]
      rw [← Torsor.add_assoc (-(a / b)) (a / b) (-j)]
      rw [Torsor.add_left_neg (a / b)]
      rw [Torsor.add_comm (Torsor.zero P) (-j)]
      rw [Torsor.add_zero]
    rw [← Torsor.add_assoc (-(p / a) + -(a / b)) (-(a / b)) (-j)]
    rw [h2]
    have h3 : -(p / a) + -(a / b) = -(p / b) := by
      rw [← Torsor.neg_add (p / a) (a / b)]
      rw [Torsor.add_comm (p / a) (a / b)]
      rw [pitch_sub_add_pitch_sub a b p]
    rw [h3]

theorem srInterval_srInterval_general (i j : I) (a b p : P) :
  srInterval i a (srInterval j b p) = rInterval ((a / b) + (a / b) + (j - i)) p := by
  rw [srInterval_change_center j a b p]
  rw [srInterval_srInterval]
  unfold rInterval
  have :  (a / b + a / b + (j - i)) • p = (a / b + a / b + j + -i) • p := by
    rw [Torsor.sub_eq_add_neg]
    rw [← Torsor.add_assoc (a / b + a / b) j (-i)]
  rw [this]
  rw [Torsor.sub_eq_add_neg]

instance : Mul (@TransposeAction P I) where
  mul
  | .r i, .r j => .r (i + j)
  | .r i, .sr a j => .sr a (j - i)
  | .sr a i, .r j => .sr a (i + j)
  | .sr a i, .sr b j => .r ((a / b) + (a / b) + (j - i))

theorem transposeAction_mul_smul (t1 t2 : @TransposeAction P I) (p : P) :
  t1 • (t2 • p) = (t1 * t2) • p := by
  cases t1 <;> cases t2 <;> simp [HMul.hMul, Mul.mul]
  unfold HSMul.hSMul instHSMul SMul.smul instSMulTransposeAction
  simp
  rw [rInterval_rInterval]
  unfold HSMul.hSMul instHSMul SMul.smul instSMulTransposeAction
  simp
  rw [rInterval_srInterval]
  unfold HSMul.hSMul instHSMul SMul.smul instSMulTransposeAction
  simp
  rw [srInterval_rInterval]
  unfold HSMul.hSMul instHSMul SMul.smul instSMulTransposeAction
  simp
  rw [srInterval_srInterval_general]
