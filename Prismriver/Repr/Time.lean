import Std.Data.TreeMap
import Lean.ToExpr

namespace Prismriver

class Time (T : Type) extends Add T, Sub T, Neg T, SMul Int T, Ord T, Inhabited T, Repr T where
  zero : T
  /- Maximum time within a bar -/
  bar : T := zero
  default := zero

section

variable { T } [Time T]
instance : LT T := ltOfOrd
instance : LE T := leOfOrd
instance : Min T := minOfLe
instance : Max T := maxOfLe

structure TimeSpan [Time T] where
  start : T
  duration : T
  deriving Ord, BEq, DecidableEq

protected def TimeSpan.stop [Time T] (s : @TimeSpan T _) : T := s.start + s.duration

instance : HAdd (@TimeSpan T _) T (@TimeSpan T _) where
  hAdd span t := { start := span.start + t, duration := span.duration }

instance : Repr (@TimeSpan T _) where
  reprPrec t _ := f!"{reprPrec t.start 0}+{reprPrec t.duration 0}"

end

instance : Time Int where
  zero := 0

instance : Ord Rat where
  compare r1 r2 :=
    if r1 = r2 then
      .eq
    else if r1 < r2 then
      .lt
    else
      .gt

instance : Time Rat where
  zero := 0
  bar := 1

open Lean in
instance : ToExpr Rat where
  toExpr t :=
    let num := toExpr t.num
    let den := toExpr (t.den : Int)
    mkAppN (mkConst ``Rat.divInt) #[num, den]
  toTypeExpr : Expr := mkConst ``Rat

structure MeasuredTime where
  bars : Int := 0
  offset : Rat := 0
  deriving Ord, BEq, DecidableEq
instance : LT MeasuredTime := ltOfOrd
instance : LE MeasuredTime := leOfOrd
instance : Min MeasuredTime := minOfLe
instance : Max MeasuredTime := maxOfLe

-- Check lexicographical ordering
example : (⟨1, 2⟩ : MeasuredTime) < (⟨2, 1⟩ : MeasuredTime) := by decide

/-- one bar -/
protected def MeasuredTime.bar : MeasuredTime := ⟨1, 0⟩

instance : Coe Rat MeasuredTime where
  coe offset := ⟨0, offset⟩

/-- Rational time -/
def rt (n d : Nat) : MeasuredTime := mkRat n d

protected def MeasuredTime.dot (m : MeasuredTime) (n : Nat := 1) : MeasuredTime :=
  let multiplier := 2 - mkRat 1 (2 ^ n)
  { bars := m.bars, offset := m.offset * multiplier }

instance : Repr MeasuredTime where
  reprPrec i _ := f!"{i.bars}.{i.offset}"
instance : ToString MeasuredTime where
  toString i := s!"{i.bars}.{i.offset}"

open Lean in
instance : ToExpr MeasuredTime where
  toExpr t :=
    let bars := toExpr t.bars
    let offset := toExpr t.offset
    mkAppN (mkConst ``MeasuredTime.mk) #[bars, offset]
  toTypeExpr : Expr := mkConst ``MeasuredTime

instance : Add MeasuredTime where
  add t1 t2 := ⟨t1.bars + t2.bars, t1.offset + t2.offset⟩
instance : Sub MeasuredTime where
  sub t1 t2 := ⟨t1.bars - t2.bars, t1.offset - t2.offset⟩
instance : Neg MeasuredTime where
  neg t := ⟨-t.bars, -t.offset⟩
instance : SMul Int MeasuredTime where
  smul n t := ⟨n * t.bars, n * t.offset⟩
instance : ShiftRight MeasuredTime where
  shiftRight t s := match s.bars with
    | 0 => ⟨t.bars, t.offset + s.offset⟩
    | b => ⟨t.bars + b, s.offset⟩

instance : Time MeasuredTime where
  zero := ⟨0, 0⟩
  bar := ⟨1, 0⟩

instance : SMul Rat MeasuredTime where
  smul n t :=
    let total := n * (t.bars + t.offset)
    ⟨ total.floor, total - total.floor ⟩

structure DivisionLine where
  onBeat : Bool := false

/-- Represents division of a time period. The ways of dividing notes
characterize music -/
structure Division (T := MeasuredTime) [Ord T] where
  lines : Std.TreeMap T DivisionLine
  --non_empty : lines.isEmpty = false

namespace Division

variable { T } [Time T]

protected def zero : Division T := {
      lines := Std.TreeMap.empty.insert Time.zero { onBeat := true },
    }
instance : Inhabited (Division T) where
  default := .zero

protected def fromLines ( times : List T ) : Division T := {
    lines := times.foldl (init := .empty) λ m t =>
      m.insert t { }
  }
protected def times (d : Division T) : List T := d.lines.keys
protected def timesArray (d : Division T) : Array T := d.lines.keysArray
protected def minTime (d : Division T) : T := d.lines.minKey!
protected def maxTime (d : Division T) : T := d.lines.maxKey!

/-- Iterate over sections -/
protected def forSectionsM { m } [Monad m] (d : Division T) (f : T → T → m Unit) : m Unit := do
  let _ : Option T := ← d.lines.foldlM (init := .none) λ t? t' _ => do
    match t? with
    | .none => pure ()
    | .some t =>
      f t t'
    pure (.some t')

end Division
