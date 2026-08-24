import Prismriver.Syntax

namespace Prismriver.Example

open Classical

def necrofantasia : Classical.Score :=
  let main := Score.fromParts [
    (0, { instrument? := .some Instrument.violin }),
  ]
  let mainline := ♩[[ c,,,, d e f5 ]]
  let violin := mainline.remapParts λ
    | .none => .some 0
    | .some _ => panic! "Invalid part id"
  main.merge violin
