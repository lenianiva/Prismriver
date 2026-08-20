import Lake
open Lake DSL
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.28.0"
package Prismriver

lean_exe prismriver where
  root := `Main

@[default_target]
lean_lib Prismriver where
  roots := #[`Prismriver]

require LSpec from git
  "https://github.com/argumentcomputer/LSpec.git" @ "b76de469ebd3ae7a6ba494a36d34f713763623a6"

lean_lib PrismriverTest {
}
@[test_driver]
lean_exe test {
  root := `PrismriverTest.Main
}
