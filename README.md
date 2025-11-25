# Prismriver

A Music representation library and DSL in Lean 4

## Roadmap

See [roadmap](doc/roadmap.typ) (need to be compiled with Typst).

## Building

Install Rust and Lean. Build the library with

``` sh
lake build
```

## Contributing

Every commit must be filtered through pre-commit hooks. Install `pre-commit`,
and run

``` sh
pre-commit install --install-hooks
```

Building the Rust part of this library requires setting some environment
variables. Create a `.envrc` file for convenience:

``` sh
export LEAN_ROOT=$(lake env printenv LEAN_SYSROOT)
export DYLD_LIBRARY_PATH=$LEAN_ROOT/lib/lean
```

These variables are automatically set by the Lean build script, and are
therefore unnecessary for developing the Lean part.

## Contributors 
(Leni Aniva)[https://leni.sh]
(Claire Wang)[https://clairewang.net]
