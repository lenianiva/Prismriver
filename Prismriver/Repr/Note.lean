import Prismriver.Repr.Scale
import Prismriver.Repr.Time

import Lean.ToExpr

namespace Prismriver

structure Note (P D : Type) where
  pitch : P
  duration : D
  deriving BEq, Ord

instance [Ord P] [Ord D] : LT (Note P D) := ltOfOrd
instance [Ord P] [Ord D] : LE (Note P D) := leOfOrd

instance [Repr P] [Repr D] : Repr (Note P D) where
  reprPrec n p := f!"{reprPrec n.pitch p}[{reprPrec n.duration p}]"
instance [ToString P] [ToString D] : ToString (Note P D) where
  toString n := s!"{n.pitch}[{n.duration}]"

open Lean in
instance [ToExpr P] [ToExpr D] : ToExpr (Note P D) where
  toExpr n :=
    let pitch := toExpr n.pitch
    let duration := toExpr n.duration
    mkAppN (mkConst ``Note.mk) #[pitch, duration]
  toTypeExpr : Expr := mkConst ``Note
