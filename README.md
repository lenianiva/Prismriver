# Prismriver

A Music formalizatzion library and DSL in Lean 4 for:

1. Formalization of music theory including pitches, accidentals, scales, chords, durations, parts
2. Algorithmic analysis (e.g. key estimation) and composition (counterpoint)
3. Mathematical modeling of music
4. Lilypond compatible music syntax

## Playback

Prismriver supports playback using [Alda](https://alda.io/). Alda is optional,
but it is necessary for playing music.

This command plays the first 5 notes of Necrofantasia

```lean
import Prismriver
#play ♩[e4 c'4 b4 d4 e2]
```

## Contributing

Every commit must be filtered through pre-commit hooks. Install `prek`,
and run

``` sh
prek install
```

See [roadmap](doc/roadmap.typ) (need to be compiled with Typst).

## Contributors

- [Leni Aniva](https://leni.sh)
- [Claire Wang](https://clairewang.net)
