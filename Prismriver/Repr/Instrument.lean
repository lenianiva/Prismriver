import Prismriver.Repr.Classical

namespace Prismriver

variable { P I } [HAdd P I P]

structure Instrument where
  name : String
  /-- Generated harmonics relative to fundamental tone -/
  harmonics : List Rat := []
  /-- Physical notes generated on a scale -/
  scale : Scale P I

/-- Sine wave generator -/
def sine : Instrument (P := Int) (I := Int) := {
  name := "sine"
  scale := et12,
}

/-- Equally-tempered acoustic grand piano -/
def acoustic_grand : Instrument (P := Int) (I := Int) := {
  name := "acoustic_grand"
  harmonics := [
    12,
    12 + 7,
    12 * 2 + 5,
    12 * 2 + 7,
  ],
  scale := et12,
}
