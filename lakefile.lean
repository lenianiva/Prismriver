import Lake
open System Lake DSL

package Prismriver

extern_lib libprismriver pkg := do
  proc { cmd := "cargo", args := #["build", "--release"], cwd := pkg.dir }
  let name := nameToStaticLib "prismriver"
  let srcPath := pkg.dir / "target" / "release" / name
  IO.FS.createDirAll pkg.staticLibDir
  let tgtPath := pkg.staticLibDir / name
  IO.FS.writeBinFile tgtPath (← IO.FS.readBinFile srcPath)
  return (pure tgtPath)

@[default_target]
lean_exe prismriver where
  root := `Main

@[default_target]
lean_lib Prismriver where
  roots := #[`Prismriver]
  precompileModules := true
