# Prismriver

A Music formalization library and DSL in Lean 4 for:

1. Formalization of music theory including pitches, accidentals, scales, chords,
   durations, parts
2. Algorithmic analysis (e.g. key estimation) and composition (counterpoint)
3. Mathematical modeling of music
4. Lilypond compatible music syntax

## Structure

### Tuning and Scale

Scales are handled in [Scale.lean](Prismriver/Repr/Scale.lean) and
[Classical.lean](Prismriver/Repr/Classical.lean). We do not distinguish between
tuning systems and scales. A `PseudoScale` is a list of pitches. A `Scale` is a
list of pitches with a fundamental interval. This flexibility handles
xenharmonic tuning systems that are not based on Western music theory. Equal
temperament is a scale. A `Tuning` system maps one scale to another. For
example, under the equal temperament tuning system, C♯ and D♭ are enharmonic.

[Classical.lean](Prismriver/Repr/Classical.lean) handles Western Classical
music. Each pitch is the combination of a name (`Hep`), an accidental, and an
octave, with the octave being the fundamental interval. An interval has a letter
distance and a semitone distance. We can transpose a note using arithmetic
operations `+` and `-`. In some sense, the intervals form a group action on
pitches. This also recalls properties of affine spaces.

Whether an interval is consonant or dissonant is dependent on the physical
properties of the instrument and this varies across cultures, and hence the
choice of consonant intervals is left as free parameters in composition
algorithms. We still provide convenient shortcuts such as `p5` or `ma6` for
intervals.

### Time

We handle time, the other axis of music, in
[Time.lean](Prismriver/Repr/Time.lean). To allow arbitrary musical sequences,
the most general form of time only consists of an instance type `I` and a
duration type `D`. `MeasuredTime` is a representation based on bars and rational
offsets.

### Algorithmic Composition

Implemented in [Composition](Prismriver/Composition). We implemented
[Counterpoint](Prismriver/Composition/Counterpoint.lean) composition.

### Syntax and Playback

A [LilyPond](https://lilypond.org/)-like DSL is provided in
[Syntax.lean](Prismriver/Syntax.lean).

Prismriver supports playback using [Alda](https://alda.io/). Alda is optional,
but it is necessary for playing music.

This command plays the first 5 notes of Necrofantasia

```lean
import Prismriver
#play ♩[e4 c'4 b4 d4 e2]
```

## Contributing

Every commit must pass through pre-commit hooks. Install `prek` (provided in
[`shell.nix`](shell.nix)), and run

``` sh
prek install
```

See [roadmap](doc/roadmap.typ) (need to be compiled with Typst).

## Contributors

- [Leni Aniva](https://leni.sh)
- [Claire Wang](https://clairewang.net)
