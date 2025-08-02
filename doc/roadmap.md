# Roadmap

Prismriver fulfills 3 objectives:

1. It serves as a DSL to write sheet music in Lean
2. It enables mathematical analysis of music
3. It enables programmatic generation of music

## Syntax

The main syntax category is `music`:

Example:
```
set reference c4
set key .b.flat.minor
set timesignature 4/4

e f ...
```

The notation for individual notes follows the Lilypond convention, but the
directives for infrequent operations are different.
