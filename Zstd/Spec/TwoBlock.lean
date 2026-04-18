import Zstd.Spec.TwoBlockBase
import Zstd.Spec.TwoBlockCompressed
import Zstd.Spec.TwoBlockComplete

/-!
# Zstandard Two-Block Specifications (Re-export)

Historical aggregation of the two-block theorems for `decompressBlocksWF`
and `decompressFrame`. The material now lives in three submodules:

- `Zstd.Spec.TwoBlockBase` — step theorems, `WellFormedSimpleBlocks`,
  raw/RLE structural compositions and block-level completeness,
  `parseFrameHeader` lemmas, and frame wrapping helper.
- `Zstd.Spec.TwoBlockCompressed` — two-block theorems involving at least
  one compressed block (literals or sequences), the unified
  `WellFormedBlocks` induction predicate, and composed completeness
  theorems for all compressed-block combinations.
- `Zstd.Spec.TwoBlockComplete` — frame-level composed completeness and
  content characterization for raw/RLE two-block frames.

This file is retained so downstream imports of `Zstd.Spec.TwoBlock`
continue to work.
-/
