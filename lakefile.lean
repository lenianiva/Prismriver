import Lake
open Lake DSL

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
