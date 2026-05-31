import Lean.ToExpr

namespace Prismriver

class Time (T : Type) extends Add T, Sub T, Neg T, SMul Int T, Ord T where
  zero : T
  /- Maximum time within a bar -/
  bar : T := zero

section

set_option synthInstance.checkSynthOrder false

variable { T } [Time T]
instance : LT T := ltOfOrd
instance : LE T := leOfOrd
instance : Min T := minOfLe
instance : Max T := maxOfLe
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
  deriving Ord, BEq
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
    | b => ⟨t.bars + s.bars, s.offset⟩

instance : Time MeasuredTime where
  zero := ⟨0, 0⟩
  bar := ⟨1, 0⟩
