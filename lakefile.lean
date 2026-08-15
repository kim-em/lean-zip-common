import Lake
open System Lake DSL

package «lean-zip-common» where
  testDriver := "test"

-- Both libraries are default targets, so a bare `lake build` (what CI runs)
-- actually builds them. Without this Lake has nothing to do and reports
-- "Build completed successfully (0 jobs)".
--
-- `.andSubmodules`, not `.submodules`: the latter excludes the root module
-- itself, so `ZipForStd.lean`/`ZipCommon.lean` were left out of the library.
-- A shared library built from such a lib has no `initialize_<lib>` symbol, and
-- a dependent package with `precompileModules := true` then fails to load it
-- ("error loading plugin, initializer not found
-- 'initialize_lean_x2dzip_x2dcommon_ZipForStd'").
@[default_target]
lean_lib ZipForStd where
  globs := #[.andSubmodules `ZipForStd]

@[default_target]
lean_lib ZipCommon where
  globs := #[.andSubmodules `ZipCommon]

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
