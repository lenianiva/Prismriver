import Lake
open Lake DSL

package Prismriver

extern_lib libprismriver pkg := do
  let leanRoot := (← Lean.getBuildDir).toString
  proc {
    cmd := "cargo", args := #["build", "--release", "--lib"],
    cwd := pkg.dir, env := #[("LEAN_ROOT", .some leanRoot)],
  }
  let name := nameToSharedLib "prismriver"
  let srcPath := pkg.dir / "target" / "release" / name
  IO.FS.createDirAll pkg.sharedLibDir
  let dstPath := pkg.sharedLibDir / name
  IO.FS.writeBinFile dstPath (← IO.FS.readBinFile srcPath)
  return (pure dstPath)

lean_exe prismriver where
  root := `Main

@[default_target]
lean_lib Prismriver where
  roots := #[`Prismriver]
  precompileModules := true
