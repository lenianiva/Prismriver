import Lean.ToExpr

namespace Prismriver

class Time (I D : Type) extends Add D, HAdd I D I, Neg D, SMul Int D where
  zero : D
  /- Maximum time within a bar -/
  bar : D := zero

instance : Time Int Int where
  zero := 0

instance : Time Rat Rat where
  zero := 0

instance : Ord Rat where
  compare r1 r2 :=
    if r1 = r2 then
      .eq
    else if r1 < r2 then
      .lt
    else
      .gt

open Lean in
instance : ToExpr Rat where
  toExpr t :=
    let num := toExpr t.num
    let den := toExpr (t.den : Int)
    mkAppN (mkConst ``Rat.divInt) #[num, den]
  toTypeExpr : Expr := mkConst ``Rat

structure MeasuredTime where
  bar : Int := 0
  offset : Rat := 0
  deriving Ord
instance : LT MeasuredTime := ltOfOrd
instance : LE MeasuredTime := leOfOrd

instance : ToString MeasuredTime where
  toString i := s!"{i.bar}.{i.offset}"

open Lean in
instance : ToExpr MeasuredTime where
  toExpr t :=
    let bar := toExpr t.bar
    let offset := toExpr t.offset
    mkAppN (mkConst ``MeasuredTime.mk) #[bar, offset]
  toTypeExpr : Expr := mkConst ``MeasuredTime

instance timeSignature (top bot : Nat)
  : Time MeasuredTime Rat where
  zero := 0
  bar := mkRat top bot
  hAdd t d := { t with offset := t.offset + d }

instance : Time MeasuredTime Rat where
  zero := 0
  bar := mkRat 4 4
  hAdd t d := { t with offset := t.offset + d }
