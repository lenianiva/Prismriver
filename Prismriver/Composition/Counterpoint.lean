/- Dr. Youyou Cong's counterpoint -/
import Prismriver.Repr.Classical

namespace Prismriver.Composition

open Classical

def formCounterpointAux : List Pitch → Interval → List Pitch → List Pitch
  | [], _, total => total
  | [x], i, total => (x + i) :: total
  | x :: y :: xs, i, total =>
    let x' := x + i
    let i' := (2 : Int) • (x - y) + i
    formCounterpointAux (y::xs) i' (x'::total)

def formCounterpoint (notes : List Pitch) (initial : Interval) : List Pitch :=
  let result := formCounterpointAux notes initial []
  result.reverse

#eval formCounterpoint [ (.new .c 4), (.new .d 4), (.new .e 4 .flat), (.new .c 4) ] ((-1) • Interval.p5)

end Prismriver.Composition
