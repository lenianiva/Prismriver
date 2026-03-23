import Prismriver.Repr.Scale
import Prismriver.Repr.Time

import Lean.ToExpr

namespace Prismriver

structure Note (P T D : Type) [Time T D] where
  pitch : P
  time : T
  duration : D
  deriving Ord

variable [Time T D]

instance [Ord P] [Ord T] [Ord D] : LT (Note P T D) := ltOfOrd
instance [Ord P] [Ord T] [Ord D] : LE (Note P T D) := leOfOrd

instance [ToString P] [ToString T] [ToString D] : ToString (Note P T D) where
  toString n := s!"{n.pitch} {n.time} {n.duration}"

open Lean in
instance [ToExpr P] [ToExpr T] [ToExpr D] : ToExpr (Note P T D) where
  toExpr n :=
    let pitch := toExpr n.pitch
    let time := toExpr n.time
    let duration := toExpr n.duration
    mkAppN (mkConst ``Note.mk) #[pitch, time, duration]
  toTypeExpr : Expr := mkConst ``Note
