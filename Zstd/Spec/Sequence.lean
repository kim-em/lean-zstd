import Zstd.Spec.Sequence.Primitives
import Zstd.Spec.Sequence.Header
import Zstd.Spec.Sequence.FseTable
import Zstd.Spec.Sequence.FseTablesComposition
import Zstd.Spec.Sequence.Completeness
import Zstd.Spec.Sequence.Validity
import Zstd.Spec.Sequence.ExtraBits
import Zstd.Spec.Sequence.Execute

/-!
# Zstd Sequence Validity and Execution Invariants (aggregate module)

This module re-exports the thematic submodules of the Zstd sequence
specification. The contents were split from a single large file; see the
submodules under `Zstd.Spec.Sequence.*` for the actual definitions and
theorems.
-/
