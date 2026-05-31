import Prismriver.Repr.Classical

namespace Prismriver

def midiInstruments : Array String := #[
    "",
    "acoustic grand",
    "bright acoustic",
    "electric grand",
    "honky-tonk",
    "electric piano 1",
    "electric piano 2",
    "harpsichord",
    "clav",
    "celesta",
    "glockenspiel",
    "music box",
    "vibraphone",
    "marimba",
    "xylophone",
    "tubular bells",
    "dulcimer",
    "drawbar organ",
    "percussive organ",
    "rock organ",
    "church organ",
    "reed organ",
    "accordion",
    "harmonica",
    "concertina",
    "acoustic guitar (nylon)",
    "acoustic guitar (steel)",
    "electric guitar (jazz)",
    "electric guitar (clean)",
    "electric guitar (muted)",
    "overdriven guitar",
    "distorted guitar",
    "guitar harmonics",
    "acoustic bass",
    "electric bass (finger)",
    "electric bass (pick)",
    "fretless bass",
    "slap bass 1",
    "slap bass 2",
    "synth bass 1",
    "synth bass 2",
    "violin",
    "viola",
    "cello",
    "contrabass",
    "tremolo strings",
    "pizzicato strings",
    "orchestral harp",
    "timpani",
    "string ensemble 1",
    "string ensemble 2",
    "synthstrings 1",
    "synthstrings 2",
    "choir aahs",
    "voice oohs",
    "synth voice",
    "orchestra hit",
    "trumpet",
    "trombone",
    "tuba",
    "muted trumpet",
    "french horn",
    "brass section",
    "synthbrass 1",
    "synthbrass 2",
    "soprano sax",
    "alto sax",
    "tenor sax",
    "baritone sax",
    "oboe",
    "english horn",
    "bassoon",
    "clarinet",
    "piccolo",
    "flute",
    "recorder",
    "pan flute",
    "blown bottle",
    "shakuhachi",
    "whistle",
    "ocarina",
    "lead 1 (square)",
    "lead 2 (sawtooth)",
    "lead 3 (calliope)",
    "lead 4 (chiff)",
    "lead 5 (charang)",
    "lead 6 (voice)",
    "lead 7 (fifths)",
    "lead 8 (bass+lead)",
    "pad 1 (new age)",
    "pad 2 (warm)",
    "pad 3 (polysynth)",
    "pad 4 (choir)",
    "pad 5 (bowed)",
    "pad 6 (metallic)",
    "pad 7 (halo)",
    "pad 8 (sweep)",
    "fx 1 (rain)",
    "fx 2 (soundtrack)",
    "fx 3 (crystal)",
    "fx 4 (atmosphere)",
    "fx 5 (brightness)",
    "fx 6 (goblins)",
    "fx 7 (echoes)",
    "fx 8 (sci-fi)",
    "sitar",
    "banjo",
    "shamisen",
    "koto",
    "kalimba",
    "bagpipe",
    "fiddle",
    "shanai",
    "tinkle bell",
    "agogo",
    "steel drums",
    "woodblock",
    "taiko drum",
    "melodic tom",
    "synth drum",
    "reverse cymbal",
    "guitar fret noise",
    "breath noise",
    "seashore",
    "bird tweet",
    "telephone ring",
    "helicopter",
    "applause",
    "gunshot",
  ]

structure Instrument where
  name : String
  midiInstrument? : Option Nat := .none

namespace Instrument

/-- Sine wave generator -/
def sine : Instrument := {
  name := "sine"
}

/-- Equally-tempered acoustic grand piano -/
def acoustic_grand : Instrument := {
  name := "Acoustic Grand",
  midiInstrument? := .some 1,
}

/-- Equally-tempered violin -/
def violin : Instrument := {
  name := "Violin"
  midiInstrument? := .some 41,
}

/-- Describes the dominant harmonics of an instrument -/
class Harmonics ( P I ) (inst : Instrument) where
  scale : Scale P I
  harmonics : List I
  lowest : Option P := .none
  highest : Option P := .none

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

open EqualTemp in
instance : Harmonics Int Int acoustic_grand where
  scale := et12
  harmonics := et12StringHarmonics
  lowest := .some (c4 - octave * 3 - 2)
  highest := .some (c4 + octave * 4)

open EqualTemp in
instance : Harmonics Int Int violin where
  scale := et12
  harmonics := et12StringHarmonics
  lowest := .some (c4 - 3)
  highest := .some (c4 + octave * 3)
