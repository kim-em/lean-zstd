import Zstd.Spec.Content.Single
import Zstd.Spec.Content.CompressedFirst
import Zstd.Spec.Content.SimpleFirst
import Zstd.Spec.Content.TwoCompressed

/-!
# Zstandard Frame Specification — Content Characterization (aggregate module)

This module re-exports the thematic submodules of the frame-level content
characterization. The contents were split from a single large file; see the
submodules under `Zstd.Spec.Content.*` for the actual theorems.
-/
