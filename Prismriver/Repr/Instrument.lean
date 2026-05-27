import Prismriver.Repr.Classical

namespace Prismriver

variable ( P )

structure Instrument where
  name : String
  lowest : Option P := .none
  highest : Option P := .none

namespace Instrument

/-- Sine wave generator -/
def sine : Instrument (P := Int) := {
  name := "sine"
}

open EqualTemp in
/-- Equally-tempered acoustic grand piano -/
def acoustic_grand : Instrument (P := Int) := {
  name := "acoustic_grand"
  lowest := .some (c4 - octave * 3 - 2),
  highest := .some (c4 + octave * 4),
}

open EqualTemp in
/-- Equally-tempered violin -/
def violin : Instrument (P := Int) := {
  name := "violin"
  lowest := .some (c4 - 3),
  highest := .some (c4 + octave * 3),
}

/-- Describes the dominant harmonics of an instrument -/
class Harmonics ( I ) (inst : Instrument P) where
  scale : Scale P I
  harmonics : List I

/-- Dominant harmonics for strings in ET12 tuning -/
def et12StringHarmonics : List Int := [
  12,
  12 + 7,
  12 * 2,
  12 * 2 + 5,
  12 * 2 + 7,
]

/-- Sine wave generator has no harmonics -/
instance (n : Nat) : Harmonics Int Int sin where
  scale := EqualTemp.scale n
  harmonics := []

instance : Harmonics Int Int acoustic_grand where
  scale := et12
  harmonics := et12StringHarmonics

instance : Harmonics Int Int violin where
  scale := et12
  harmonics := et12StringHarmonics
