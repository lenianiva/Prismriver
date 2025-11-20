import Prismriver.Repr.Scale
import Prismriver.Repr.Time

namespace Prismriver

variable (P D I : Type)
variable [HAdd P I P] [Scale P I]
variable [Add D] [HAdd T D T] [HSub T T D] [SMul Int D] [SMul D I]

structure Note (P T D : Type) where
  pitch : P
  time : T
  duration : D

instance [ToString P] [ToString T] [ToString D] : ToString (Note P T D) where
  toString n := s!"{n.pitch} {n.time} {n.duration}"
