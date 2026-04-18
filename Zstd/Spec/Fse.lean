import Zstd.Spec.Fse.Basic
import Zstd.Spec.Fse.ProbsGeNeg1
import Zstd.Spec.Fse.Distribution
import Zstd.Spec.Fse.BackwardBitReader
import Zstd.Spec.Fse.BitPos
import Zstd.Spec.Fse.BuildTable
import Zstd.Spec.Fse.Predefined
import Zstd.Spec.Fse.Symbols

/-!
# FSE distribution and table validity (aggregate module)

This module re-exports the thematic submodules of the FSE specification.
The contents were split from a single large file; see the submodules
under `Zstd.Spec.Fse.*` for the actual definitions and theorems.
-/
