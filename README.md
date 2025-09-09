# Prismriver

A Music DSL in Lean 4

## Building

Install `cargo` and `elan`. Then run

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
