import Lean.Data.RBTree

open Lean

namespace Prismriver

/-- A scale is a set of pitches -/
class PseudoScale (P : Type) where
  name : String

/-- We make no distinction between scales and tuning systems. They are
represented by the same class. For example, a tuning system could be represented
as a scale with raw frequencies, and any abstract scale could be lifted into the
raw frequency scale. This would represent tuning. -/
class Tuning (P₁ P₂ : Type) (src : PseudoScale P₁) (dst : PseudoScale P₂) where
  liftPitch : P₁ → P₂

/-- A scale with a repeating fundamental interval. Each pitch in the scale is
represented as a tone along with a multiple of the fundamental interval. -/
class Scale (P I : Type) extends PseudoScale P, Add I, Sub I, HMul Int I I, Neg I, HSMul I P P, HDiv P P I where
  /-- The fundamental interval (usually an octave) -/
  fundamental : I
  /-- List all notes in the 0th interval. e.g. For C major, this would be C,D,E,F,G,A,B -/
  pitches : List P

  zero : I
  add_zero (i : I) : i + zero = i
  add_comm (i j : I) : i + j = j + i
  add_assoc (i j k : I) : (i + j) + k = i + (j + k)
  add_left_neg (i : I) : (-i) + i = zero
  add_right_neg (i : I) : i + (-i) = zero := by
    rw [add_comm]
  sub_neg (i j : I) : i - (-j) = i + j
  sub_eq_add_neg (i j : I) : i - j = i + -j
  neg_neg (i : I) : -(-i) = i
  neg_sub (i j : I) : -(i - j) = j - i := by
    simp [sub_neg, add_comm, Int.neg_add]
  neg_add (i j : I) : -(i + j) = -i + -j
  zero_mul (i : I) : (0 : Int) * i = zero

  mul_distrib (n m : Int) (i : I) : (n + m) * i = n * i + m * i
  neg_mul (i : I) (n : Int) : (-n) * i = -(n * i)

  smul_zero (p : P) : zero • p = p
  smul_assoc (p : P) (i j : I) : j • (i • p) = (i + j) • p
  smul_div (p q : P) : (q / p) • p = q
  div_smul_self (i : I) (p : P) : (i • p) / p = i

variable { P I }

def pitchCong [scale : Scale P I] (φ : I) (p q : P) :=
  ∃ (n : Int), p = (n * φ) • q

theorem pitchCong_equivalence [scale : Scale P I] (φ : I) : Equivalence (@pitchCong (P := P) (I := I) scale φ) :=
  {
    refl p := by
      unfold pitchCong
      apply Exists.intro 0
      simp [scale.zero_mul, scale.smul_zero]
    ,
    symm hcong := by
      unfold pitchCong at *
      rcases hcong with ⟨n, h⟩
      apply Exists.intro (-n)
      simp [h, scale.neg_mul, scale.smul_assoc, scale.add_right_neg, scale.smul_zero]
    ,
    trans hpqc hqrc := by
      unfold pitchCong at *
      rcases hpqc with ⟨npq, hpq⟩
      rcases hqrc with ⟨nqr, hqr⟩
      apply Exists.intro (npq + nqr)
      rewrite [hpq, hqr]
      simp [scale.mul_distrib, scale.smul_assoc, scale.add_comm]
    ,
  }

set_option synthInstance.checkSynthOrder false in
/-- Equivalence classes of pitches -/
instance pitchSetoid [scale : Scale P I] (φ : I := scale.fundamental) : Setoid P where
  r := pitchCong φ
  iseqv := pitchCong_equivalence φ

/-- Equivalence of pitch classes -/
abbrev pitchClass [scale : Scale P I] (φ : I := scale.fundamental)
   := Quotient (@pitchSetoid P I scale φ)

/-- Ordered list of notes. To accomodate for inversions, this is not ordered. -/
abbrev Chord P := List P

namespace EqualTemp

abbrev Pitch := Int
abbrev Interval := Int

instance scale (n : Nat) : Scale Pitch Interval where
  name := s!"{n}-ET"
  fundamental := n
  pitches := List.finRange n |>.map (·.toNat)
  hSMul i j := i + j
  hDiv p q := p - q

  zero := 0
  add_zero := Int.add_zero
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  add_left_neg := Int.add_left_neg
  add_right_neg := Int.add_right_neg
  sub_neg := Int.sub_neg
  sub_eq_add_neg := by apply Int.sub_eq_add_neg
  neg_sub := Int.neg_sub
  neg_neg := Int.neg_neg
  neg_add := by apply Int.neg_add
  zero_mul := Int.zero_mul
  neg_mul i j := by
    apply Int.neg_mul
  mul_distrib := Int.add_mul
  smul_zero := Int.zero_add
  smul_assoc p i j := by
    rw [Int.add_comm i p, Int.add_comm, Int.add_comm _ p, Int.add_assoc]
  smul_div p q := by
    apply Int.sub_add_cancel
  div_smul_self i p := by
    rw [Int.add_sub_cancel]

theorem n_et_notes (n : Nat) : (scale n).pitches.length = n := by
  unfold Scale.pitches
  unfold scale
  rewrite [List.length_map]
  apply List.length_finRange

abbrev et12 := scale 12

/-- MIDI C4 -/
def c4 : Pitch := 60
def octave : Interval := 12

end EqualTemp

export EqualTemp (et12)
