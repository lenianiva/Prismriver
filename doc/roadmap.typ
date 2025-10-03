#show link: it => underline(text(fill: blue)[#it])

#align(center, text(17pt)[
  *Prismriver: A Music DSL and Representation Library in Lean 4*
])

#grid(
  columns: (1fr, 1fr, 1fr),
  align(center)[
    Leni Aniva \
    Stanford University \
    #link("mailto:aniva@stanford.edu")
  ],
  align(center)[
    Claire Wang \
    University of Pennsylvania \
      #link("mailto:cdwang@seas.upenn.edu")
  ],
  align(center)[
    Chris Henson \
    Drexel University \
    #link("mailto:ch3474@drexel.edu")
  ],
)

== Motivation

Prismriver aims to fulfil 3 obejctives:

1. Formalization the mathematical analysis of music.
2. Music representation using a DSL
3. Programmatic generation of music

Lean is a proof assistant with rapidly growing popularity, and actively
maintained infrastructure support. Lean's flexible and extensible syntax system
allows us to implement a DSL for music. The highly structured nature of music
means it could be represented as text, version controlled, and analysed
programmatically. Lean also has the unique advantage of mathlib4, which can be
used for formalizing analysis of music.

In order for Prismriver to be compatible with existing music infrastructure, it
can parse/generate MusicXML. Meanwhile it is also compatible with xenharmonic
systems and exotic tuning systems.

#link("https://codeberg.org/aniva/Prismriver")

== Representation

Internal representation of musical objects must be sufficiently versatile and
expressive for Prismriver to be used as a music analysis tool.

=== Scale and Tuning

A `PseudoScale` is a set of permitted pitches. For example, the set of all
possible frequencies is a `PseudoScale`. A *Scale* is a `PseudoScale` with a
repeating unit. In this respect, a scale is a group with a fundamental period
$r$ and the permitted pitches in a scale are equivalent classes modulo $r$. This
enables representation of xenharmonic systems.

Each scale is associated with pitch type. In classical music
(`Prismriver.Classical`), the pitches are triplets of octave, name, and
accidental. This representation allows for non-equally-tempered tuning systems.

A tuning system in Prismriver is a map (`PseudoScaleLift`) from a `Scale` to a
more fundamental `PseudoScale`. For example, 12-tone equal temperament tuning is
a map from a classical scale to the chromatic scale. An interval is represented
as a number along with an accidental.

=== Time

The representation of time is based on MusicXML. Like scales, there are two
layers of time representation. The `Time` class is an abstract representation of
time which imposes no restrictions on the type of time. A `Metre` is a subclass
of `Time` which has rational times and should be used for writing music. The
reason for this decision is that musical directives may change the actual
passage of time compared to the notation (e.g. fermata). `Nat` is an instance of
`Time`, which is handy for analyzing simple progressions without the concept of
bars.

== Music Algorithms

=== Counterpoint

We aim to represent counterpoint using Prismriver's existing DSL primitives. We
are interested in the following:

1. Provide library support to enable users to write proofs about Counterpoint
  theory.
2. Ability to sonify Prismriver's counterpoint representation.

It might be possible to use coinduction with counterpoint theory.

Species counterpoint are different sets of rules for composing counterpoint. We
aim to provide a first species class that can be extended to higher species. A
user can compose within species constraints and prove properties about species.

=== Key Estimation

With the help of probability theory libraries, we can perform key estimation by
evaluating the probability that a music piece is of a particular key.

== Engineering

=== Scales

A diatonic scale in western music theory is specified with a root tone (which
can be e.g. $A sharp$, or $C natural$) with a modus. The modus is a tone name
for which the scale pattern matches the scale formed by the 7 natural tones
immediately after the given name. For example, the E-Dorian scale is
`diatonic .e.natural .d`, since $D,E,F,G,A,B,C$ forms a Dorian scale.

```lean
structure Tone where
  name : Hep
  acc : Accidental := .natural
  deriving BEq, Inhabited
instance diatonic (root : Tone) (modus : Hep) : Scale Tone where
  name := s!"{root} {modus.modus}"
  tones := ... -- 7 tones of the scale
```

Without a tuning system, enharmonic tones are fundamentally different. e.g.
$.e.natural eq.not .f.flat$.

=== Music Sequence Representation

```lean
def part1 : Part := {
  reference := `c4,
  key := .b.flat.minor,
  timesignature := ⟨4, 4⟩,
  notes := ♩[ c4 c d d e e | f f g g a a ]
}
```

=== MIDI Interface

The `#play` macro calls into the system MIDI library to play a snippet. This
feature is inspired by Alda.

```lean
#play [c4 c d d e e]
```

=== LilyPond

To avoid the tedium of writing Lean notation for music, we can use LilyPond
notation to succintly represent music.
