import Lake
open System Lake DSL

package «lean-zip-common» where
  testDriver := "test"

-- Both libraries are default targets, so a bare `lake build` (what CI runs)
-- actually builds them. Without this Lake has nothing to do and reports
-- "Build completed successfully (0 jobs)".
@[default_target]
lean_lib ZipForStd where
  globs := #[.submodules `ZipForStd]

@[default_target]
lean_lib ZipCommon where
  globs := #[.submodules `ZipCommon]

-- IO FFI (Handle seek/fileSize shims — no external library deps)
input_file io_ffi.c where
  path := "c" / "io_ffi.c"
  text := true

target io_ffi.o pkg : FilePath := do
  let srcJob ← io_ffi.c.fetch
  let oFile := pkg.buildDir / "c" / "io_ffi.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  let hardArgs := if Platform.isWindows then #[] else #["-fPIC"]
  buildO oFile srcJob weakArgs hardArgs "cc"

extern_lib libio_ffi pkg := do
  let ffiO ← io_ffi.o.fetch
  let name := nameToStaticLib "io_ffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]
