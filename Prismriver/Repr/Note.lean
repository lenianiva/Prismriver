import Prismriver.Repr.Pitch
import Prismriver.Repr.Duration

namespace Prismriver

structure Note (P : Type) [Scale P] where
  pitch : P
  duration : Duration
