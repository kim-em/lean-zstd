import Zstd.Spec.Succeeds
import Zstd.Spec.Content
import Zstd.Spec.Complete

/-!
# Zstandard Frame Specification (RFC 8878) — Re-export

This file re-exports the three sub-modules:
- `ZstdSucceeds`: Frame-level "succeeds" theorems and block-loop composition helpers
- `ZstdContent`: Content characterization theorems
- `ZstdComplete`: Unified completeness theorem via `WellFormedBlocks`

Base definitions are in `Zip/Spec/ZstdBase.lean`.
Block-loop structural lemmas are in `Zip/Spec/ZstdBlockLoop.lean`.
Block-level two-block compositions are in `Zip/Spec/ZstdTwoBlock.lean`.
-/
