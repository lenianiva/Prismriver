import Prismriver.Syntax

namespace Prismriver.Example

open Classical

set_option maxRecDepth 1000 in
def necrofantasia : Classical.Score :=
  let main := Score.fromParts [
    (0, { instrument? := .some Instrument.violin }),
  ]
  let mainline := ♩[[
    e''4 c' b d,8 e | e''2.. r8  |
    e4      d'   c b8 c8 | c'''4  b a g8 a8 |
    a4      g    e g8 a8 | a''4   g e g8   e  |
    e4      d  e g8  e | e''2..          r8  |
    e''4 c' b d,8 e | e''2..          r8  |
    e''4   d'   c b8 c8 | c'''4  b a g8 a  |
    a''4   g    e g8  a | a''4   g e g8 a' |
    a'1                    | a'2.. r8 |

    c''4 e  d  b8 c8 | c2..      r8   |
    c4    d  e  d8 e8 | e4 d c b8 c8  |
    c4    b  a  b8 c8 | c4 b a b8 a8  |
    a4    b  c  b8 c8 | c2..      r8   |
    a'4  e' d  b8 c8 | c2..      r8   |
    c4    d  e  d8 e8 | e4 d c b8 c8  |
    c4    b  a  b8 c8 | c4 b a b8 cs8 |
    cs1                 | cs2..       r8   |
  ]]
  let violin := mainline.remapParts λ
    | .none => .some 0
    | .some _ => panic! "Invalid part id"
  main.merge violin
