import Prismriver.Repr.Scale
import Prismriver.Repr.Duration

namespace Prismriver

structure Note { P I : Type } [HAdd P I P] [Scale P I] where
  pitch : P
  duration : Duration
