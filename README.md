# Prismriver

A Music representation library and DSL in Lean 4

## Example

This command plays the first 5 notes of Necrofantasia

```lean
import Prismriver
#play ["e4", "> c4", "b4", "< d4", "e4~4"]
```

## Building

Install and Lean. Build the library with

``` sh
lake build
```

To play MIDI, install `alda`.

## Contributing

Every commit must be filtered through pre-commit hooks. Install `prek`,
and run

``` sh
prek install
```

See [roadmap](doc/roadmap.typ) (need to be compiled with Typst).

## Contributors

[Leni Aniva](https://leni.sh)

[Claire Wang](https://clairewang.net)
