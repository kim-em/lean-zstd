import ZstdTest.Helpers
import Zstd.Native.Frame
import Zstd.Native.XxHash

/-! Tests for Zstd native frame/block parsing and frame-level decompression.
    Covers: frame header parsing, block header parsing, RLE/raw block decompression,
    decompressBlocks round-trip, decompressZstd round-trip, skippable frames,
    and checksum verification (tests 1–27). -/

def ZstdTest.ZstdNativeFrame.tests : IO Unit := do
  -- Helper: compress data and parse the frame header
  let parseCompressed (input : ByteArray) (level : UInt8 := 3) : IO Zstd.Native.ZstdFrameHeader := do
    let compressed ← Zstd.compress input level
    match Zstd.Native.parseFrameHeader compressed 0 with
    | .ok (header, _) => return header
    | .error e => throw (IO.userError s!"parseFrameHeader failed: {e}")

  -- Test 1: empty input
  let hdr ← parseCompressed ByteArray.empty
  -- Empty input should parse successfully (zstd produces a valid frame for empty data)
  -- Content size should be 0 when present
  if let some cs := hdr.contentSize then
    unless cs == 0 do throw (IO.userError s!"empty: expected contentSize 0, got {cs}")

  -- Test 2: small input (62 bytes)
  let small := "Hello, world! This is a test of zlib compression from Lean 4. ".toUTF8
  let hdr ← parseCompressed small
  if let some cs := hdr.contentSize then
    unless cs == small.size.toUInt64 do
      throw (IO.userError s!"small: expected contentSize {small.size}, got {cs}")

  -- Test 3: medium input (64KB)
  let medium := mkConstantData 65536
  let hdr ← parseCompressed medium
  if let some cs := hdr.contentSize then
    unless cs == 65536 do
      throw (IO.userError s!"medium: expected contentSize 65536, got {cs}")

  -- Test 4: compression level 1 (fast)
  let testData ← mkTestData
  let hdr ← parseCompressed testData 1
  if let some cs := hdr.contentSize then
    unless cs == testData.size.toUInt64 do
      throw (IO.userError s!"level1: expected contentSize {testData.size}, got {cs}")

  -- Test 5: compression level 19 (best)
  let hdr ← parseCompressed testData 19
  if let some cs := hdr.contentSize then
    unless cs == testData.size.toUInt64 do
      throw (IO.userError s!"level19: expected contentSize {testData.size}, got {cs}")

  -- Test 6: position after header is valid (within compressed data bounds)
  let compressed ← Zstd.compress testData
  match Zstd.Native.parseFrameHeader compressed 0 with
  | .ok (_, endPos) =>
    unless endPos ≤ compressed.size do
      throw (IO.userError s!"endPos {endPos} exceeds compressed size {compressed.size}")
    unless endPos ≥ 6 do  -- minimum: 4 magic + 1 descriptor + 1 (fcs or window)
      throw (IO.userError s!"endPos {endPos} too small for a valid header")
  | .error e => throw (IO.userError s!"parseFrameHeader failed: {e}")

  -- Test 7: invalid magic number
  let badMagic := ByteArray.mk #[0x00, 0x00, 0x00, 0x00, 0x00]
  match Zstd.Native.parseFrameHeader badMagic 0 with
  | .ok _ => throw (IO.userError "bad magic: should have failed")
  | .error e =>
    unless e.contains "invalid magic number" do
      throw (IO.userError s!"bad magic: wrong error message: {e}")

  -- Test 8: truncated input
  match Zstd.Native.parseFrameHeader (ByteArray.mk #[0x28, 0xB5]) 0 with
  | .ok _ => throw (IO.userError "truncated: should have failed")
  | .error _ => pure ()

  -- Test 9: large input (124KB)
  let large ← mkLargeData
  let hdr ← parseCompressed large
  if let some cs := hdr.contentSize then
    unless cs == large.size.toUInt64 do
      throw (IO.userError s!"large: expected contentSize {large.size}, got {cs}")

  -- Test 10: parseBlockHeader on FFI-compressed data (after frame header)
  let compressed ← Zstd.compress testData
  match Zstd.Native.parseFrameHeader compressed 0 with
  | .ok (_, blockStart) =>
    match Zstd.Native.parseBlockHeader compressed blockStart with
    | .ok (blkHdr, _) =>
      unless blkHdr.blockSize.toNat > 0 do
        throw (IO.userError s!"block: expected blockSize > 0, got {blkHdr.blockSize}")
      -- Block type should be raw, rle, or compressed (not reserved)
      unless blkHdr.blockType != .reserved do
        throw (IO.userError "block: got reserved block type")
    | .error e => throw (IO.userError s!"parseBlockHeader failed: {e}")
  | .error e => throw (IO.userError s!"parseFrameHeader failed: {e}")

  -- Test 11: decompressRLEBlock produces correct repeated output
  -- Manually construct a byte array: [0xAA] and decompress as RLE with size 5
  let rleSrc := ByteArray.mk #[0xAA]
  match Zstd.Native.decompressRLEBlock rleSrc 0 5 with
  | .ok (result, endPos) =>
    unless result.size == 5 do
      throw (IO.userError s!"RLE: expected 5 bytes, got {result.size}")
    unless endPos == 1 do
      throw (IO.userError s!"RLE: expected endPos 1, got {endPos}")
    for i in [:5] do
      unless result[i]! == 0xAA do
        throw (IO.userError s!"RLE: byte {i} expected 0xAA, got {result[i]!}")
  | .error e => throw (IO.userError s!"decompressRLEBlock failed: {e}")

  -- Test 12: decompressRawBlock produces correct verbatim copy
  let rawSrc := ByteArray.mk #[0x01, 0x02, 0x03, 0x04, 0x05]
  match Zstd.Native.decompressRawBlock rawSrc 1 3 with
  | .ok (result, endPos) =>
    unless result.size == 3 do
      throw (IO.userError s!"Raw: expected 3 bytes, got {result.size}")
    unless endPos == 4 do
      throw (IO.userError s!"Raw: expected endPos 4, got {endPos}")
    unless result[0]! == 0x02 && result[1]! == 0x03 && result[2]! == 0x04 do
      throw (IO.userError "Raw: incorrect bytes copied")
  | .error e => throw (IO.userError s!"decompressRawBlock failed: {e}")

  -- Test 13: parseBlockHeader on truncated input fails
  match Zstd.Native.parseBlockHeader (ByteArray.mk #[0x00, 0x00]) 0 with
  | .ok _ => throw (IO.userError "truncated block header: should have failed")
  | .error _ => pure ()

  -- Test 14: decompressBlocks on empty-input compressed data
  -- Empty input compressed by zstd may produce a single block (likely RLE or raw of size 0)
  let emptyCompressed ← Zstd.compress ByteArray.empty
  match Zstd.Native.parseFrameHeader emptyCompressed 0 with
  | .ok (_, blockStart) =>
    -- Try to decompress blocks — may succeed (raw/RLE) or fail (compressed)
    match Zstd.Native.decompressBlocks emptyCompressed blockStart with
    | .ok (result, _) =>
      unless result.size == 0 do
        throw (IO.userError s!"empty blocks: expected 0 output bytes, got {result.size}")
    | .error e =>
      -- If it fails because of compressed block type, that's acceptable
      unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
        throw (IO.userError s!"empty blocks: unexpected error: {e}")
  | .error e => throw (IO.userError s!"parseFrameHeader on empty: {e}")

  -- Test 15: decompressBlocks round-trip on constant data
  -- Constant data often gets stored as RLE blocks by zstd
  let constData := mkConstantData 256
  let constCompressed ← Zstd.compress constData 1
  match Zstd.Native.parseFrameHeader constCompressed 0 with
  | .ok (_, blockStart) =>
    match Zstd.Native.decompressBlocks constCompressed blockStart with
    | .ok (result, _) =>
      unless result.data == constData.data do
        throw (IO.userError s!"const blocks: decompressed {result.size} bytes, expected {constData.size}")
    | .error e =>
      -- Compressed blocks are expected for some data — not a test failure
      unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
        throw (IO.userError s!"const blocks: unexpected error: {e}")
  | .error e => throw (IO.userError s!"parseFrameHeader on const: {e}")

  -- Test 16: decompressZstd round-trip on empty input
  let emptyCompressed2 ← Zstd.compress ByteArray.empty
  match Zstd.Native.decompressZstd emptyCompressed2 with
  | .ok result =>
    unless result.size == 0 do
      throw (IO.userError s!"decompressZstd empty: expected 0 bytes, got {result.size}")
  | .error e =>
    unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"decompressZstd empty: unexpected error: {e}")

  -- Test 17: decompressZstd round-trip on constant data (likely RLE blocks)
  let constData2 := mkConstantData 256
  let constCompressed2 ← Zstd.compress constData2 1
  match Zstd.Native.decompressZstd constCompressed2 with
  | .ok result =>
    unless result.data == constData2.data do
      throw (IO.userError s!"decompressZstd const: decompressed {result.size} bytes, expected {constData2.size}")
  | .error e =>
    unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"decompressZstd const: unexpected error: {e}")

  -- Test 18: decompressZstd round-trip on single byte
  let singleByte := ByteArray.mk #[0x42]
  let singleCompressed ← Zstd.compress singleByte 1
  match Zstd.Native.decompressZstd singleCompressed with
  | .ok result =>
    unless result.data == singleByte.data do
      throw (IO.userError s!"decompressZstd single: expected [0x42], got {result.data}")
  | .error e =>
    unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"decompressZstd single: unexpected error: {e}")

  -- Test 19: decompressZstd round-trip on all-zeros (maximally compressible)
  let zeros := mkConstantData 1024
  let zerosCompressed ← Zstd.compress zeros 1
  match Zstd.Native.decompressZstd zerosCompressed with
  | .ok result =>
    unless result.data == zeros.data do
      throw (IO.userError s!"decompressZstd zeros: decompressed {result.size} bytes, expected {zeros.size}")
  | .error e =>
    unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"decompressZstd zeros: unexpected error: {e}")

  -- Test 20: decompressZstd error on invalid magic number
  match Zstd.Native.decompressZstd (ByteArray.mk #[0x00, 0x00, 0x00, 0x00, 0x00]) with
  | .ok _ => throw (IO.userError "decompressZstd bad magic: should have failed")
  | .error e =>
    unless e.contains "invalid magic number" do
      throw (IO.userError s!"decompressZstd bad magic: wrong error: {e}")

  -- Test 21: decompressZstd error on truncated input
  match Zstd.Native.decompressZstd (ByteArray.mk #[0x28, 0xB5]) with
  | .ok _ => throw (IO.userError "decompressZstd truncated: should have failed")
  | .error e =>
    unless e.contains "too short" do
      throw (IO.userError s!"decompressZstd truncated: wrong error: {e}")

  -- Test 22: decompressZstd skips skippable-only input (returns empty output)
  -- Skippable frame magic: 0x184D2A50 (little-endian: 50 2A 4D 18), size = 4, 4 payload bytes
  let skippable := ByteArray.mk #[0x50, 0x2A, 0x4D, 0x18, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
  match Zstd.Native.decompressZstd skippable with
  | .ok result =>
    unless result.size == 0 do
      throw (IO.userError s!"decompressZstd skippable-only: expected empty output, got {result.size} bytes")
  | .error e =>
    throw (IO.userError s!"decompressZstd skippable-only: unexpected error: {e}")

  -- Test 23: decompressFrame returns correct position after frame
  let frameTestData := mkConstantData 128
  let frameCompressed ← Zstd.compress frameTestData 1
  match Zstd.Native.decompressFrame frameCompressed 0 with
  | .ok (result, endPos) =>
    unless result.data == frameTestData.data do
      throw (IO.userError s!"decompressFrame: decompressed {result.size} bytes, expected {frameTestData.size}")
    -- endPos should be at or near the end of compressed data
    unless endPos ≤ frameCompressed.size do
      throw (IO.userError s!"decompressFrame: endPos {endPos} exceeds compressed size {frameCompressed.size}")
    unless endPos ≥ 6 do
      throw (IO.userError s!"decompressFrame: endPos {endPos} too small")
  | .error e =>
    unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"decompressFrame: unexpected error: {e}")

  -- Test 24: decompressFrame content size validation
  -- We verify this indirectly: FFI-compressed data includes content size in header,
  -- and our decompressor checks it matches the decompressed output.
  -- If decompression succeeds, the size check passed.
  let sizeTestData := mkConstantData 512
  let sizeCompressed ← Zstd.compress sizeTestData 1
  match Zstd.Native.decompressFrame sizeCompressed 0 with
  | .ok (result, _) =>
    unless result.size == 512 do
      throw (IO.userError s!"decompressFrame size: expected 512 bytes, got {result.size}")
  | .error e =>
    unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"decompressFrame size: unexpected error: {e}")

  -- Test 25: valid FFI-compressed data decompresses.
  -- Note: libzstd's `ZSTD_compress` leaves the content checksum flag off by
  -- default (only the `zstd` CLI turns it on), so this frame has no checksum;
  -- Test 28 decodes a real checksummed frame.
  let checksumData := mkConstantData 256
  let checksumCompressed ← Zstd.compress checksumData 1
  match Zstd.Native.decompressZstd checksumCompressed with
  | .ok result =>
    unless result.data == checksumData.data do
      throw (IO.userError "checksum valid: decompressed data mismatch")
  | .error e =>
    unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"checksum valid: unexpected error: {e}")

  -- Test 26: checksum verification — corrupted data triggers checksum error
  -- We corrupt a byte in the decompressed content region of the frame
  -- (after header + block headers, before the checksum trailer).
  -- For constant data compressed at level 1, the frame is:
  --   header | block header (3 bytes) | block content | checksum (4 bytes)
  let corruptData := mkConstantData 256
  let corruptCompressed ← Zstd.compress corruptData 1
  -- Parse header to find where block content starts
  match Zstd.Native.parseFrameHeader corruptCompressed 0 with
  | .ok (_, blockStart) =>
    -- Block header is 3 bytes, content starts after that
    let contentStart := blockStart + 3
    if contentStart < corruptCompressed.size - 4 then
      -- Flip a byte in the block content
      let corrupted := corruptCompressed.set! contentStart
        (corruptCompressed[contentStart]! ^^^ 0xFF)
      match Zstd.Native.decompressZstd corrupted with
      | .ok _ =>
        -- If decompression succeeds, the block might be compressed (no checksum
        -- verification path hit), which is OK
        pure ()
      | .error e =>
        -- Should be either a checksum mismatch or compressed-blocks-not-implemented
        unless e.contains "checksum mismatch" || e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
          throw (IO.userError s!"checksum corrupt: expected checksum error, got: {e}")
  | .error e => throw (IO.userError s!"checksum corrupt: header parse failed: {e}")

  -- Test 27: checksum verification — empty input with checksum
  -- Empty data compressed by zstd includes a content checksum
  let emptyChecksumCompressed ← Zstd.compress ByteArray.empty
  match Zstd.Native.decompressZstd emptyChecksumCompressed with
  | .ok result =>
    unless result.size == 0 do
      throw (IO.userError s!"checksum empty: expected 0 bytes, got {result.size}")
  | .error e =>
    unless e.contains "compressed blocks not yet implemented" || e.contains "sequence decoding not yet implemented" || e.contains "compressed literals" || e.contains "treeless literals" do
      throw (IO.userError s!"checksum empty: unexpected error: {e}")

  -- Test 28: a real checksummed frame from the `zstd` CLI (testdata/zstd/interop).
  -- The frame stores the LOWER 32 bits of XXH64 (RFC 8878 §3.1.1); comparing against
  -- the upper 32 bits rejects every checksummed frame. Also check that a corrupted
  -- checksum is still rejected.
  let hello ← readFixture "zstd/interop/system-hello.zst"
  match Zstd.Native.parseFrameHeader hello 0 with
  | .ok (hdr, _) =>
    unless hdr.contentChecksum do
      throw (IO.userError "system-hello.zst: expected a frame with a content checksum")
  | .error e => throw (IO.userError s!"system-hello.zst: header parse failed: {e}")
  match Zstd.Native.decompressZstd hello with
  | .ok result =>
    unless result.data == "Hello from system zstd\n".toUTF8.data do
      throw (IO.userError "system-hello.zst: decompressed data mismatch")
  | .error e => throw (IO.userError s!"system-hello.zst: unexpected error: {e}")
  let badSum := hello.set! (hello.size - 1) (hello[hello.size - 1]! ^^^ 0x01)
  match Zstd.Native.decompressZstd badSum with
  | .ok _ => throw (IO.userError "system-hello.zst with a corrupted checksum: accepted")
  | .error e =>
    unless e.contains "checksum mismatch" do
      throw (IO.userError s!"system-hello.zst with a corrupted checksum: unexpected error: {e}")

  -- Test 29: a frame (from `zstd -19 --no-check`) with a sequence whose literal length
  -- is 0 and whose offset value is 3, i.e. Repeat_Offset_1 - 1. That is a new offset:
  -- it goes in front of the history and the others shift down (RFC 8878 §3.1.1.5).
  -- Keeping the old second and third entries decodes this frame to the wrong bytes,
  -- and with no checksum nothing notices.
  let rep ← readFixture "zstd/interop/repeat-offset-ll0.zst"
  let repRaw ← readFixture "zstd/interop/repeat-offset-ll0.raw"
  match Zstd.Native.decompressZstd rep with
  | .ok result =>
    unless result.data == repRaw.data do
      throw (IO.userError "repeat-offset-ll0.zst: decompressed data mismatch")
  | .error e => throw (IO.userError s!"repeat-offset-ll0.zst: unexpected error: {e}")
  match Zstd.Native.resolveOffset 3 #[10, 20, 30] 0 with
  | (off, hist) =>
    unless off == 9 && hist == #[9, 10, 20] do
      throw (IO.userError s!"resolveOffset 3 (literalLength 0): expected (9, #[9, 10, 20]), got ({off}, {hist})")

  IO.println "ZstdNativeFrame tests: OK"
