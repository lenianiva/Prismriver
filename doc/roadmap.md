# Roadmap

Prismriver fulfills 3 objectives:

1. It serves as a DSL to write sheet music in Lean
2. It enables mathematical analysis of music
3. It enables programmatic generation of music

In order for Prismriver to be useful as a music analysis tool, it has to be
compatible with many systems:

1. Xenharmonic scales and tuning systems
2. MusicXML

## Structure

Prismriver is compatible with xenharmonic scales, tuning systems, and times. It
is also compatible with MIDI representation of music.

Internally, there is little distinction between scales and tuning systems. A
tuning system for a scale is a `PseudoScaleLift` class instance, which maps from
the pitches of the scale to a `PseudoScale`. For example, we can have a
`PseudoScale` with all "pitches" being raw frequencies, and a tuning system maps
pitches (e.g. C5) to a raw pitch.

A `Scale` is a `PseudoScale` with a repeating minimal unit. Most commonly, this
unit is the octave.

## Syntax

The main syntax category for writing notes is `music`. Outside of this syntax
category, we use the normal Lean syntax.

Example:
```lean4
def part1 : Part := {
  reference := `c4,
  key := .b.flat.minor,
  timesignature := ⟨4, 4⟩,
  notes := ♩[ c4 c d d e e | f f g g a a ]
}
```

The notation for individual notes follows the LilyPond convention.
