import Prismriver.Repr.Classical

namespace Prismriver

variable ( P )

structure Instrument where
  name : String
  /-- Physical notes generated on a scale -/
  scale : Scale P
  /-- Generated harmonics relative to fundamental tone -/
  harmonics : List scale.I := []
  lowest : Option P := .none
  highest : Option P := .none

namespace Instrument

/-- Sine wave generator with no harmonics -/
def sine : Instrument (P := Int) := {
  name := "sine"
  scale := et12,
}

/-- Dominant harmonics for strings in ET12 tuning -/
def et12StringHarmonics : List Int := [
  12,
  12 + 7,
  12 * 2,
  12 * 2 + 5,
  12 * 2 + 7,
]

/-- Equally-tempered acoustic grand piano -/
def acoustic_grand : Instrument (P := Int) := {
  name := "acoustic_grand"
  scale := et12,
  harmonics := et12StringHarmonics,
}

/-- Equally-tempered violin -/
def violin : Instrument (P := Int) := {
  name := "violin"
  scale := et12,
  harmonics := et12StringHarmonics,
}
