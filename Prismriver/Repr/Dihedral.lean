import Prismriver.Repr.Scale
import Prismriver.Repr.Note
import Lean.ToExpr

namespace Prismriver

open Lean

variable { P I } [scale : Scale P I]

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
  rw [← scale.add_comm]
  rw [scale.smul_assoc]

theorem rInterval_srInterval (i j : I) (a p : P) : rInterval i (srInterval j a p) = srInterval (j - i) a p := by
  unfold rInterval srInterval
  rw [scale.smul_assoc]
  congr
  have h1 : - (j - i) = -j + i := by
    sorry
  sorry

theorem hSub_hAdd_Pitch (p a : P) (j : I) : (j • p) / a = (p / a) + j := by
  sorry

theorem srInterval_rInterval (i j : I) (a p : P) :
    srInterval i a (rInterval j p) = srInterval (i + j) a p := by
  unfold srInterval rInterval
  sorry

theorem srInterval_srInterval (i j : I) (p a : P) : srInterval i a (srInterval j a p) = rInterval (j - i) p := by
  unfold srInterval rInterval
  sorry

theorem pitch_sub_add_pitch_sub (a b p : P) : (a / b) + (p / a) = p / b := by
  sorry

theorem srInterval_change_center
    (j : I) (a b p : P) :
    srInterval j b p = srInterval ((a / b) + (a / b) + j) a p := by
  sorry

theorem srInterval_srInterval_general (i j : I) (a b p : P) :
  srInterval i a (srInterval j b p) = rInterval ((a / b) + (a / b) + (j - i)) p := by
  rw [srInterval_change_center j a b p]
  rw [srInterval_srInterval]
  unfold rInterval
  sorry

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
