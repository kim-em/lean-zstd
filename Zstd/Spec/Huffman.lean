import Zstd.Spec.Huffman.Weights
import Zstd.Spec.Huffman.Table
import Zstd.Spec.Huffman.LiteralsSection
import Zstd.Spec.Huffman.TreeDescriptor
import Zstd.Spec.Huffman.Decode
import Zstd.Spec.Huffman.Completeness

/-!
# Huffman decoding specification (aggregate module)

This module re-exports the thematic submodules of the Huffman
specification. The contents were split from a single large file; see the
submodules under `Zstd.Spec.Huffman.*` for the actual definitions and
theorems.
-/
