/- Dr. Youyou Cong's counterpoint -/
import Prismriver.Repr.Classical

namespace Prismriver.Composition

open Classical

def formCounterpointAux : List Pitch → Interval → List Pitch → List Pitch
  | [], _, total => total
  | [x], i, total => (x + i) :: total
  | x :: y :: xs, i, total =>
    let x' := x + i
    let i' := (2 : Int) • (x - y) + i
    formCounterpointAux (y::xs) i' (x'::total)

def formCounterpoint (notes : List Pitch) (initial : Interval) : List Pitch :=
  let result := formCounterpointAux notes initial []
  result.reverse

#eval formCounterpoint [ (.new .c 4), (.new .d 4), (.new .e 4 .flat), (.new .c 4) ] ((-1) • Interval.p5)

def allowedIntervalMovement (i : Interval) : Prop :=
  i = Interval.p4 ∨ i = Interval.p5
  ∨ i = Interval.ma3 ∨ i = Interval.mi3
  ∨ i = Interval.ma7 ∨ i = Interval.mi7

def allowedIntervalBegin (i : Interval) : Prop :=
  i = Interval.p4 ∨ i = Interval.p5 ∨ i = Interval.octave

def allowedIntervalEnd (i : Interval) : Prop :=
  i = Interval.p4 ∨ i = Interval.octave

def isFirstSpecies
  (lhs rhs : List Pitch)
  {heq : lhs.length = rhs.length}
  {h : lhs.length ≠ 0}
  (consonant movement intervalMovement : Interval → Prop)
  (beginInterval := allowedIntervalBegin)
  (endInterval := allowedIntervalEnd)
  : Prop :=
  let beginAllowed :=
    let interval := lhs[0] - rhs[0]
    beginInterval interval
  let part1 := ∀ i, ∀ h : i < lhs.length,
    let l := lhs[i]
    let r := rhs[i]
    let interval := l - r
    consonant interval
  let part2 := ∀ i, ∀ h : i < lhs.length - 1,
    let l1 := lhs[i]
    let l2 := lhs[i+1]
    let r1 := rhs[i]
    let r2 := rhs[i+1]
    let m := l2 - l1
    movement m ∧ (m = (r2 - r1) ∨ m = (r1 - r2)) ∧
    intervalMovement m
  let part3 := ∀ i, ∀ h : i < lhs.length - 1,
    let l1 := lhs[i]
    let r1 := rhs[i]
    l1 != r1
  let endAllowed :=
    let interval := lhs[lhs.length-1] - rhs[lhs.length-1]
    endInterval interval

  part1 ∧ part2 ∧ part3 ∧ beginAllowed ∧ endAllowed

def myCantus := [Pitch.new .c 4, Pitch.new .d 4, Pitch.new .e 4 .flat, Pitch.new .c 4]
def myCounterpoint := formCounterpoint myCantus ((-1) • Interval.p5)

theorem myCounterpoint_valid :
    isFirstSpecies myCantus myCounterpoint
      (heq : myCantus.length = myCounterpoint.length)
      (h : myCantus.length ≠ 0)
    :=
    have part1 := intros
    have part2 := sorry
    have part3 := sorry
    have beginAllowed := sorry
    have endAllowed := sorry
    sorry


end Prismriver.Composition
