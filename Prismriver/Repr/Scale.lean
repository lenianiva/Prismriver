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
class Scale (P) extends PseudoScale P where
  I : Type
  add : Add I
  hAdd : HAdd P I P
  hSub : HSub P P I
  sMul: SMul Int I
  neg : Neg I
  /-- The fundamental interval (usually an octave) -/
  fundamental : I
  /-- List all notes in the 0th interval. e.g. For C major, this would be C,D,E,F,G,A,B -/
  pitches : List P

  zero : I
  neg_add (i : I) : i + (-i) = zero
  add_zero (i : I) : i + zero = i
  add_comm (i j : I) : i + j = j + i
  add_assoc (i j k : I) : (i + j) + k = i + (j + k)

  zero_mul (i : I) : (0 : Int) • i = zero
  mul_distrib (n m : Int) (i : I) : (n + m) • i = n • i + m • i
  neg_mul (i : I) (n : Int) : (-n) • i = -(n • i)

  add_pitch_zero (p : P) : p + zero = p
  add_pitch_assoc (p : P) (i j : I) : (p + i) + j = p + (i + j)

def pitchCong [scale : Scale P] (φ : scale.I) (p q : P) :=
  let _ := scale.sMul
  let _ := scale.hAdd
  ∃ (n : Int), p = q + n • φ

theorem pitchCong_equivalence [scale : Scale P] (φ : scale.I) : Equivalence (pitchCong φ) :=
  {
    refl p := by
      unfold pitchCong
      simp
      apply Exists.intro 0
      simp [scale.zero_mul, scale.add_pitch_zero]
    ,
    symm hcong := by
      unfold pitchCong at *
      simp at *
      rcases hcong with ⟨n, h⟩
      apply Exists.intro (-n)
      simp [h, scale.neg_mul, scale.add_pitch_assoc, scale.neg_add, scale.add_pitch_zero]
    ,
    trans hpqc hqrc := by
      unfold pitchCong at *
      simp at *
      rcases hpqc with ⟨npq, hpq⟩
      rcases hqrc with ⟨nqr, hqr⟩
      apply Exists.intro (npq + nqr)
      rewrite [hpq, hqr]
      simp [scale.mul_distrib, scale.add_pitch_assoc, scale.add_comm]
    ,
  }

/-- Equivalence classes of pitches -/
instance pitchSetoid [scale : Scale P] (φ : scale.I := scale.fundamental) : Setoid P where
  r := pitchCong φ
  iseqv := pitchCong_equivalence φ

/-- Equivalence of pitch classes -/
abbrev pitchClass [scale : Scale P] (φ : scale.I := scale.fundamental)
   := Quotient (pitchSetoid φ)

/-- Ordered list of notes. To accomodate for inversions, this is not ordered. -/
abbrev Chord P := List P

namespace EqualTemp

abbrev Pitch := Int
abbrev Interval := Int

instance scale (n : Nat) : Scale Pitch where
  I := Interval
  hAdd := @instHAdd Int Int.instAdd
  hSub := @instHSub Int Int.instSub
  sMul := @instSMulOfMul Int Int.instMul
  add := Int.instAdd
  neg := Int.instNegInt
  name := s!"{n}-ET"
  fundamental := n
  pitches := List.finRange n |>.map (·.toNat)

  zero := 0
  neg_add i := by
    rewrite [Int.add_neg_eq_sub]
    apply Int.sub_self
  add_zero := Int.add_zero
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  zero_mul := Int.zero_mul
  mul_distrib := Int.add_mul
  add_pitch_zero := Int.add_zero
  add_pitch_assoc := Int.add_assoc
  neg_mul i j := by
    apply Int.neg_mul


theorem n_et_notes (n : Nat) : (scale n).pitches.length = n := by
  unfold Scale.pitches
  unfold scale
  rewrite [List.length_map]
  apply List.length_finRange

abbrev et12 := scale 12

end EqualTemp

export EqualTemp (et12)
