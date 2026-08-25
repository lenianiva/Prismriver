import Prismriver.Syntax

namespace Prismriver.Example

open Classical

set_option maxRecDepth 1000 in
def necrofantasia : Classical.Score :=
  let main := Score.fromParts [
    (0, { instrument? := .some Instrument.violin }),
  ]
  let chords := ♩[[
    <e'1 g'1 b'1> | <e'1 g'1 b'1> |
    <e'1 a'1 c''1> | <g'1 b'1 d''1> |
    <e'1 g'1 b'1> | <c'1 e'1 g'1> |
    <e'1 g'1 b'1> | <e'1 g'1 b'1> |

    <e'1 g'1 b'1> | <e'1 g'1 b'1> |
    <e'1 a'1 c''1> | <g'1 b'1 d''1> |
    <e'1 g'1 b'1> | <c'1 e'1 g'1> |
    <a1 cs'1 e'1> | <a1 cs'1 e'1> |

    -- fine

    <a1 c'1 e'1> | <a1 c'1 e'1> |
    <e'1 g'1 b'1> | <e'1 g'1 b'1> |
    <a1 c'1 e'1> | <a1 c'1 e'1> |
    <a1 c'1 e'1> | <a1 c'1 e'1> |

    <a1 c'1 e'1> | <a1 c'1 e'1> |
    <e'1 g'1 b'1> | <e'1 g'1 b'1> |
    <a1 c'1 e'1> | <a1 c'1 e'1> |
    <a1 c'1 e'1> | <a1 c'1 e'1> |
  ]]
  let main := main.merge chords
  let mainline := ♩[[
    e'4 c''4 b'4 d'8 e'8 | e'2.. r8  |
    e'4      d''4   c''4 b'8 c''8 | c''4  b'4 a'4 g'8 a'8 |
    a'4      g'4    e'4 g'8 a'8 | a'4   g'4 e'4 g'8   e'8  |
    e'4      d'4  e'4 g'8  e'8 | e'2..          r8  |
    e'4 c''4 b'4 d'8 e'8 | e'2..          r8  |
    e'4   d''4   c''4 b'8 c''8 | c''4  b'4 a'4 g'8 a'8  |
    a'4   g'4    e'4 g'8  a'8 | a'4   g'4 e'4 g'8 <cs'8 a'8> |
    <cs'1 a'1>                    | <cs'2.. a'2..> r8 |

    c'4 e'4  d'4  b8 c'8 | c'2..      r8   |
    c'4    d'4  e'4  d'8 e'8 | e'4 d'4 c'4 b8 c'8  |
    c'4    b4  a4  b8 c'8 | c'4 b4 a4 b8 a8  |
    a4    b4  c'4  b8 c'8 | c'2..      r8   |
    a4  e'4 d'4  b8 c'8 | c'2..      r8   |
    c'4    d'4  e'4  d'8 e'8 | e'4 d'4 c'4 b8 c'8  |
    c'4    b4  a4  b8 c'8 | c'4 b4 a4 b8 cs'8 |
    cs'1                  | cs'2..       r8   |
  ]]
  let violin := mainline.remapParts λ
    | .none => .some 0
    | .some _ => panic! "Invalid part id"
  main.merge violin
