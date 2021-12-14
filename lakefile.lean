import Lake

open System Lake DSL

-- def cDir : FilePath := "c"
-- def ffiSrc := cDir / "ffi.cpp"
-- def buildDir := defaultBuildDir

-- def ffiOTarget (pkgDir : FilePath) : FileTarget :=
--   let oFile := pkgDir / buildDir / cDir / "ffi.o"
--   let srcTarget := inputFileTarget <| pkgDir / ffiSrc
--   fileTargetWithDep oFile srcTarget fun srcFile => do
--     compileO oFile srcFile #["-I", (← getLeanIncludeDir).toString] "c++"

-- def cLibTarget (pkgDir : FilePath) : FileTarget :=
--   let libFile := pkgDir / buildDir / cDir / "libffi.a"
--   staticLibTarget libFile #[ffiOTarget pkgDir]

-- package mathlib where
--   -- As mathlib does not produce an executable,
--   -- we set the default "facet" to `oleans`,
--   -- so that we can use `lake build`.
--   -- defaultFacet := PackageFacet.oleans
--   libRoots := #[`Ffi]
--   -- specify the lib as an additional target
--   moreLibTargets := #[cLibTarget "."]

package mathlib {
  -- customize layout
  binRoot := `Mathlib.Graph
  -- srcDir := "Mathlib"
  -- libRoots := #[`mathlib]
  -- specify the lib as an additional target
  -- moreLibTargets := #[cLibTarget pkgDir]
}
