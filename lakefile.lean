import Lake
open Lake DSL

require mathlib4 from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.25.1"

package Prismriver

lean_exe prismriver where
  root := `Main

@[default_target]
lean_lib Prismriver where
  roots := #[`Prismriver]
  precompileModules := true
@[test_driver]
lean_exe test {
  root := `Test.Main
}
