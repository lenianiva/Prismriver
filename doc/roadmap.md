# Roadmap

Prismriver fulfills 3 objectives:

1. It serves as a DSL to write sheet music in Lean
2. It enables mathematical analysis of music
3. It enables programmatic generation of music

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
