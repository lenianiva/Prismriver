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
Prismriver aims to achieve the following:
1. To formalize mathematical analysis of music.
2. Programmatic generation of music. 
3. DSL to write sheet music and other file formats of music.

Lean is a proof assistant with rapidly growing popularity, and actively maintained infrastructure support. Lean's flexible and extensible syntax system allows us to implement a DSL for
music. The highly structured nature of music means it could be represented as
text, version controlled, and analysed programmatically. Lean also has the unique advantage of mathlib4, which can be used for formalizing analysis of music.

== Representation

Internal representation of musical objects must be sufficiently versatile and
expressive for Prismriver to be used as a music analysis tool.

=== Scale

A `PseudoScale` is a list of permitted pitches. A *Scale* is a `PseudoScale`
with a repeating unit. In this respect, a scale is a group with a fundamental
period $r$ and the permitted pitches in a scale are equivalent classes modulo
$r$. This enables representation of xenharmonic systems.

Each scale is associated with pitch type. In classical music
(`Prismriver.Classical`), the pitches are triplets of octave, name, and
accidental. This representation allows for non-equally-tempered tuning systems.

A tuning system in Prismriver is just a `PseudoScale` with "pitches" being raw
frequencies.

=== Time

The representation of time is based on MusicXML. Like scales, there are two
layers of time representation. The `Time` class is an abstract representation of
time which imposes no restrictions on the type of time. A `Metre` is a subclass
of `Time` which has rational times and should be used for writing music. The
reason for this decision is that musical directives may change the actual
passage of time compared to the notation (e.g. fermata).

== Music Algorithms

=== Counterpoint Theory
We aim to represent counterpoint using Prismriver's existing DSL primitives. We are interested in the following:
1. Provide library support to enable users to write proofs about Counterpoint theory.
2. Ability to sonify Prismriver's counterpoint representation. 

==== Counterpoint Representation 
// note - it might be interesting to see if we can use coinduction with counterpoint theory

==== Species Counterpoint
Species counterpoint are different sets of rules for composing counterpoint. We aim to provide a first species class that can be extended to higher species. A user can compose within species constraints and prove properties about species. 

=== Key Estimation

== Engineering

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

