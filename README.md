# lean-zstd

Lean 4 Zstandard (RFC 8878) decompression: C FFI bindings and pure-Lean
implementation with formal correctness proofs.

Split from [lean-zip](https://github.com/kim-em/lean-zip).

## Features

- **FFI bindings** to libzstd for compression and decompression (whole-buffer and streaming)
- **Pure Lean decompression** -- native implementations of:
  - FSE (Finite State Entropy) decoding
  - XXHash checksumming
  - Zstd frame/block parsing
  - Huffman weight decoding
  - Sequence execution (literal copy + match copy)
- **Formal specifications** and correctness proofs in `Zstd/Spec/`

## Dependencies

- [lean-zip-common](https://github.com/kim-em/lean-zip-common) -- shared utilities

## Build

```
lake build          # build library
lake exe test       # run tests
```

Requires `libzstd-dev` (or equivalent) and `pkg-config`.

## License

Apache-2.0
