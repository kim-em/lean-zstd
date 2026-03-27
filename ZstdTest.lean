import ZstdTest.BenchHelpers
import ZstdTest.Helpers
import ZstdTest.FFI
import ZstdTest.NativeFrame
import ZstdTest.NativeComponents
import ZstdTest.NativeIntegration
import ZstdTest.Conformance
import ZstdTest.FseNative
import ZstdTest.XxHashNative
import ZstdTest.DecompressBench

def main : IO Unit := do
  unless ← System.FilePath.pathExists "testdata" do
    throw (IO.userError "testdata/ not found — run tests via 'lake test' from the project root")
  ZstdTest.Zstd.tests
  ZstdTest.ZstdNativeFrame.tests
  ZstdTest.ZstdNativeComponents.tests
  ZstdTest.ZstdNativeIntegration.tests
  ZstdTest.XxHashNative.tests
  ZstdTest.FseNative.tests
  ZstdTest.ZstdConformance.tests
  ZstdTest.ZstdDecompressBench.tests
  IO.println "\nAll tests passed!"
