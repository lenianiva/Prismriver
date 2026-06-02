/- Dr. Youyou Cong's counterpoint -/
import Prismriver.Repr
import Prismriver.Composition.Basic
import Prismriver.IO
namespace Prismriver.Composition

open Prismriver Prismriver.Classical Prismriver.Composition

def formCounterpointAux : List Pitch → Interval → List Pitch → List Pitch
  | [], _, total => total
  | [x], i, total => (i • x) :: total
  | x :: y :: xs, i, total =>
    let x' := i • x
    let i' := (2 : Int) * (x / y) + i
    formCounterpointAux (y::xs) i' (x'::total)

def formCounterpoint (notes : List Pitch) (initial : Interval) : List Pitch :=
  let result := formCounterpointAux notes initial []
  result.reverse

def allowedTerminalInterval (i : Interval) : Prop :=
    i = Interval.unison ∨ i = Interval.octave ∨ i = -Interval.octave

def contraryMotion (i j : Interval) : Prop :=
    (i.semitones > 0 ∧ j.semitones < 0) ∨
    (i.semitones < 0 ∧ j.semitones > 0)

def allowedLastNotes (lhs rhs : List Pitch) : Prop :=
    lhs.length > 1 ∧ rhs.length > 1 ∧
    let i := lhs.length - 2
    let j := rhs.length - 2
    contraryMotion
      (lhs[i+1]! / lhs[i]!)
      (rhs[j+1]! / rhs[j]!)

def isConsonance (i : Interval) : Prop :=
    i = Interval.unison ∨
    i = Interval.mi3 ∨ i = -Interval.mi3 ∨
    i = Interval.ma3 ∨ i = -Interval.ma3 ∨
    i = Interval.p5 ∨ i = -Interval.p5 ∨
    i = Interval.mi6 ∨ i = -Interval.mi6 ∨
    i = Interval.ma6 ∨ i = -Interval.ma6 ∨
    i = Interval.octave ∨ i = -Interval.octave

def isStep (i : Interval) : Prop :=
   i = Interval.mi2 ∨ i = -Interval.mi2 ∨
  i = Interval.ma2 ∨ i = -Interval.ma2

def isAllowedLeap (i : Interval) : Prop :=
    i = Interval.mi3 ∨ i = -Interval.mi3 ∨
    i = Interval.ma3 ∨ i = -Interval.ma3 ∨
    i = Interval.p4 ∨ i = -Interval.p4 ∨
    i = Interval.p5 ∨ i = -Interval.p5 ∨
    i = Interval.mi6 ∨
    i = Interval.octave ∨ i = -Interval.octave

def allowedIntervalMovement (i : Interval) : Prop :=
  isStep i ∨ isAllowedLeap i

def isTritone (i : Interval) : Prop :=
    i.semitones = 6 ∨ i.semitones = -6

def isTurningPoint (a b c : Pitch) : Prop :=
    contraryMotion (b / a) (c / b)

def noTritoneTurningPoints (melody : List Pitch) : Prop :=
  ∀ i, ∀ hi : i + 2 < melody.length,
  ∀ j, ∀ hj : j + 2 < melody.length,
    let ordered := i < j
    let tp1 := isTurningPoint melody[i] melody[i+1] melody[i+2]
    let tp2 := isTurningPoint melody[j] melody[j+1] melody[j+2]
    let outlined := melody[j+1] / melody[i+1]
    ¬ (ordered ∧ tp1 ∧ tp2) ∨ ¬ isTritone outlined

def isFirstSpecies
    (lhs rhs : List Pitch)
    {heq : lhs.length = rhs.length}
    {h : lhs.length ≠ 0}
    (consonant movement : Interval → Prop)
    (beginInterval := allowedTerminalInterval)
    (endInterval := allowedTerminalInterval)
    : Prop :=
    let beginAllowed :=
      let interval := lhs[0] / rhs[0]
      beginInterval interval

    let part1 := ∀ i, ∀ h : i < lhs.length,
      let l := lhs[i]
      let r := rhs[i]
      let interval := l / r
      consonant interval

    let part2 := ∀ i, ∀ h : i < lhs.length - 1,
      let l1 := lhs[i]
      let l2 := lhs[i+1]
      let r1 := rhs[i]
      let r2 := rhs[i+1]
      let lm := l2 / l1
      let rm := r2 / r1
      movement lm ∧ movement rm

    let part3 :=
      allowedLastNotes lhs rhs

    let endAllowed :=
      let interval := lhs[lhs.length-1] / rhs[lhs.length-1]
      endInterval interval

    let part4 :=
      noTritoneTurningPoints lhs ∧ noTritoneTurningPoints rhs

    part1 ∧ part2 ∧ part3 ∧ part4 ∧ beginAllowed ∧ endAllowed

def myCantus : List Pitch :=
    [Pitch.new .c 4, Pitch.new .d 4, Pitch.new .e 4, Pitch.new .c 4]
def myCounterpoint : List Pitch :=
    [Pitch.new .c 5, Pitch.new .b 4, Pitch.new .g 4, Pitch.new .c 5]

example : allowedLastNotes [Pitch.new .d 4, Pitch.new .c 4] [Pitch.new .b 3, Pitch.new .c 4] := by
  unfold allowedLastNotes
  unfold contraryMotion
  simp
  right
  constructor
  native_decide
  native_decide

example : allowedIntervalMovement Interval.mi2 := by
  unfold allowedIntervalMovement
  constructor
  unfold isStep
  simp

end Prismriver.Composition
