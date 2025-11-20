import Prismriver.Repr.Scale
import Prismriver.Repr.Time

namespace Prismriver

variable [HAdd P I P] [Scale P I]
variable [Add D] [HAdd T D T] [HSub T T D] [SMul Int D] [SMul D I]

structure Note where
  pitch : P
  time : T
  duration : D
