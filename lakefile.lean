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
lean_lib Test {
}
@[test_driver]
lean_exe test {
  root := `Test.Main
}
