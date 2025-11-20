import Prismriver.Repr.Scale
import Prismriver.Repr.Time

namespace Prismriver

structure Note (P : Type) [Scale P] where
  pitch : P
  duration : Duration
