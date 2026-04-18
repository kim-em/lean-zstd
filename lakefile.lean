import Lake
open System Lake DSL

/-- Get zstd include flags, respecting `ZSTD_CFLAGS` env var override. -/
def zstdCFlags : IO (Array String) := do
  if let some flags := (← IO.getEnv "ZSTD_CFLAGS") then
    return flags.trimAscii.toString.splitOn " " |>.filter (· ≠ "") |>.toArray
  let out ← IO.Process.output { cmd := "pkg-config", args := #["--cflags", "libzstd"] }
  if out.exitCode != 0 then return #[]
  return out.stdout.trimAscii.toString.splitOn " " |>.filter (· ≠ "") |>.toArray

/-- Extract `-L` library paths from `NIX_LDFLAGS` (set by nix-shell). -/
def nixLdLibPaths : IO (Array String) := do
  let some val := (← IO.getEnv "NIX_LDFLAGS") | return #[]
  return val.splitOn " " |>.filter (·.startsWith "-L") |>.toArray

/-- Get the library directory for a pkg-config package. -/
def pkgConfigLibDir (pkg : String) : IO (Option String) := do
  let out ← IO.Process.output { cmd := "pkg-config", args := #["--variable=libdir", pkg] }
  if out.exitCode != 0 then return none
  let dir := out.stdout.trimAscii.toString
  if dir.isEmpty then return none
  return some dir

/-- Find `libzstd.a` in the given `-L` directories, via pkg-config libdir,
    or via common system library directories. -/
def findStaticZstd (libPaths : Array String) : IO (Option System.FilePath) := do
  for p in libPaths do
    let dir : System.FilePath := ⟨(p.drop 2).toString⟩
    let path := dir / "libzstd.a"
    if (← path.pathExists) then return some path
  if let some dir := (← pkgConfigLibDir "libzstd") then
    let path := (⟨dir⟩ : System.FilePath) / "libzstd.a"
    if (← path.pathExists) then return some path
  for dir in #["/usr/lib/x86_64-linux-gnu", "/usr/lib/aarch64-linux-gnu",
               "/usr/lib64", "/usr/local/lib"] do
    let path := (⟨dir⟩ : System.FilePath) / "libzstd.a"
    if (← path.pathExists) then return some path
  return none

/-- Get link flags for zstd. Prefers static linking. -/
def linkFlags : IO (Array String) := do
  let libPaths ← nixLdLibPaths
  let zstdFlags ← do
    let out ← IO.Process.output { cmd := "pkg-config", args := #["--libs", "libzstd"] }
    if out.exitCode != 0 then pure #[]
    else pure (out.stdout.trimAscii.toString.splitOn " " |>.filter (· ≠ "") |>.toArray)
  let allLibPaths := libPaths ++ zstdFlags.filter (·.startsWith "-L")
  if let some zstdStaticPath := (← findStaticZstd allLibPaths) then
    if Platform.isOSX then
      let sdkPath := (← IO.Process.output {
        cmd := "xcrun", args := #["--show-sdk-path"] }).stdout.trimAscii.toString
      return allLibPaths ++ #["-lzstd", s!"-L{sdkPath}/usr/lib"]
    else
      let zstdExtra := zstdFlags.filter (fun f =>
        !f.startsWith "-L" && !f.startsWith "-lzstd" && f != "-lzstd")
      return #[zstdStaticPath.toString] ++ zstdExtra
  if !zstdFlags.isEmpty then
    if let some dir := (← pkgConfigLibDir "libzstd") then
      let soPath := (⟨dir⟩ : System.FilePath) / "libzstd.so"
      if (← soPath.pathExists) then
        return #[soPath.toString, "-Wl,--allow-shlib-undefined"]
    return zstdFlags ++ #["-Wl,--allow-shlib-undefined"]
  return libPaths ++ #["-lzstd", "-Wl,--allow-shlib-undefined"]

require zipCommon from git
  "https://github.com/kim-em/lean-zip-common" @ "main"

package «lean-zstd» where
  moreLinkArgs := run_io linkFlags
  testDriver := "test"

lean_lib Zstd

-- zstd FFI
input_file zstd_ffi.c where
  path := "c" / "zstd_ffi.c"
  text := true

target zstd_ffi.o pkg : FilePath := do
  let srcJob ← zstd_ffi.c.fetch
  let oFile := pkg.buildDir / "c" / "zstd_ffi.o"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString] ++ (← zstdCFlags)
  let hardArgs := if Platform.isWindows then #[] else #["-fPIC"]
  buildO oFile srcJob weakArgs hardArgs "cc"

extern_lib libzstd_ffi pkg := do
  let ffiO ← zstd_ffi.o.fetch
  let name := nameToStaticLib "zstd_ffi"
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

lean_lib ZstdTest where
  globs := #[.submodules `ZstdTest]

@[default_target]
lean_exe test where
  root := `ZstdTest
