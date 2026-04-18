import Zstd.Spec.FrameBase

/-!
# Zstandard Top-Level Decompressor — Simple-First Composed Completeness

Composed completeness theorems for `decompressZstd` with raw/RLE-first block
layouts. This covers:

- Single raw or single RLE block frames
- Two-block frames whose first block is raw or RLE

See `Zstd.Spec.FrameBase` for foundation lemmas and
`Zstd.Spec.FrameCompComplete` for the compressed-first analogue. -/

namespace Zstd.Spec.ZstdFrame

/-! ## decompressZstd composed completeness for raw/RLE blocks -/

/-- End-to-end composed completeness for a single raw-block frame: byte-level conditions
    on the frame header and block header imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_single_raw` (frame header + block conditions → frame success)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success)

    The header field constraints and block conditions are universally quantified over
    `(hdr, afterHdr)` from `parseFrameHeader`, since the caller doesn't know these values
    without parsing. The termination hypothesis `hterm` states that the frame fills all
    remaining data — this cannot be derived from byte-level conditions without a separate
    characterization of `decompressFrame`'s output position. -/
theorem decompressZstd_succeeds_single_raw_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zstd.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block conditions at afterHdr (byte-level raw block: type=0, lastBlock=1)
    (htypeVal : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSizeBound : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Frame terminates the data (for decompressZstdWF recursion termination)
    (hterm : ∀ content pos', Zstd.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zstd.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Specialize universally quantified hypotheses
  have htypeVal' := htypeVal hdr afterHdr hparse
  have hlastBit' := hlastBit hdr afterHdr hparse
  have hblockSizeBound' := hblockSizeBound hdr afterHdr hparse
  have hwindow' := hwindow hdr afterHdr hparse
  have hpayload' := hpayload hdr afterHdr hparse
  -- Step 3: Apply decompressFrame_succeeds_single_raw
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_single_raw
    data 0 hdr afterHdr hparse (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
    (hnosize hdr afterHdr hparse) (by omega) htypeVal' hlastBit' hblockSizeBound' hwindow' hpayload'
  -- Step 4: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-- End-to-end composed completeness for a single RLE-block frame: byte-level conditions
    on the frame header and block header imply `decompressZstd` succeeds.

    Same structure as `decompressZstd_succeeds_single_raw_frame` but for RLE blocks
    (block type = 1). RLE blocks need only 1 byte of payload (the repeated byte),
    so `hpayload` requires `afterHdr + 4` instead of `afterHdr + 3 + blockSize`. -/
theorem decompressZstd_succeeds_single_rle_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zstd.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block conditions at afterHdr (byte-level RLE block: type=1, lastBlock=1)
    (htypeVal : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSizeBound : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 4)
    -- Frame terminates the data (for decompressZstdWF recursion termination)
    (hterm : ∀ content pos', Zstd.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zstd.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Specialize universally quantified hypotheses
  have htypeVal' := htypeVal hdr afterHdr hparse
  have hlastBit' := hlastBit hdr afterHdr hparse
  have hblockSizeBound' := hblockSizeBound hdr afterHdr hparse
  have hwindow' := hwindow hdr afterHdr hparse
  have hpayload' := hpayload hdr afterHdr hparse
  -- Step 3: Apply decompressFrame_succeeds_single_rle
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_single_rle
    data 0 hdr afterHdr hparse (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
    (hnosize hdr afterHdr hparse) (by omega) htypeVal' hlastBit' hblockSizeBound' hwindow' hpayload'
  -- Step 4: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-! ## decompressZstd two-block composed completeness (rle first block) -/

/-- End-to-end composed completeness for a two-RLE-block frame: byte-level conditions
    on the frame header and both block headers imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_two_rle_blocks` (header + two RLE blocks → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_two_rle_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zstd.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block 1 (non-last RLE) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 4)
    -- Block 2 (last RLE) at off2 = afterHdr + 4
    (hsize2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 4) + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 4) + 4)
    -- Frame terminates the data
    (hterm : ∀ content pos', Zstd.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zstd.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Apply decompressFrame_succeeds_two_rle_blocks
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_two_rle_blocks
    data 0 hdr afterHdr hparse
    (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse) (hnosize hdr afterHdr hparse)
    (hsize1 hdr afterHdr hparse) (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse)
    (hpayload1 hdr afterHdr hparse) rfl
    (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse) (hlastBit2 hdr afterHdr hparse)
    (hblockSize2 hdr afterHdr hparse) (hwindow2 hdr afterHdr hparse)
    (hpayload2 hdr afterHdr hparse)
  -- Step 3: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-- End-to-end composed completeness for a frame with a non-last RLE block followed
    by a last raw block: byte-level conditions on the frame header and both block
    headers imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_rle_then_raw` (header + RLE + raw blocks → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_rle_then_raw_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zstd.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block 1 (non-last RLE) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 4)
    -- Block 2 (last raw) at off2 = afterHdr + 4
    (hsize2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 4) + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 4) + 3 +
            (((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Frame terminates the data
    (hterm : ∀ content pos', Zstd.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zstd.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Apply decompressFrame_succeeds_rle_then_raw
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_rle_then_raw
    data 0 hdr afterHdr hparse
    (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse) (hnosize hdr afterHdr hparse)
    (hsize1 hdr afterHdr hparse) (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse)
    (hpayload1 hdr afterHdr hparse) (afterHdr + 4) rfl
    (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse) (hlastBit2 hdr afterHdr hparse)
    (hblockSize2 hdr afterHdr hparse) (hwindow2 hdr afterHdr hparse)
    (hpayload2 hdr afterHdr hparse)
  -- Step 3: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-- End-to-end composed completeness for a frame with a non-last RLE block followed
    by a last compressed block with zero sequences: byte-level conditions on the frame
    header, both block headers, and the compressed block's literals/sequences parsing
    imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_rle_then_compressed_zero_seq` (header + RLE + compressed → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_rle_then_compressed_zero_seq_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zstd.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block 1 (non-last RLE) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 4)
    -- Block 2 (last compressed, zero sequences) at off2 = afterHdr + 4
    (hsize2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 4) + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hblockEnd2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 4) + 3 +
            (((data[afterHdr + 4]!.toUInt32 ||| (data[afterHdr + 4 + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 4 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Literals section and sequences header succeed for block 2
    (hparsing2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ∃ literals afterLiterals huffTree modes afterSeqHeader,
            Zstd.Native.parseLiteralsSection data (afterHdr + 4 + 3) none
              = .ok (literals, afterLiterals, huffTree) ∧
            Zstd.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader))
    -- Frame terminates the data
    (hterm : ∀ content pos', Zstd.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zstd.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Obtain literals and sequences parsing from combined hypothesis
  obtain ⟨literals, afterLiterals, huffTree, modes, afterSeqHeader, hlit2', hseq2'⟩ :=
    hparsing2 hdr afterHdr hparse
  -- Step 3: Apply decompressFrame_succeeds_rle_then_compressed_zero_seq
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_rle_then_compressed_zero_seq
    data 0 hdr afterHdr literals afterLiterals huffTree modes afterSeqHeader hparse
    (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse) (hnosize hdr afterHdr hparse)
    (hsize1 hdr afterHdr hparse) (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse)
    (hpayload1 hdr afterHdr hparse) (afterHdr + 4) rfl
    (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse) (hlastBit2 hdr afterHdr hparse)
    (hblockSize2 hdr afterHdr hparse) (hwindow2 hdr afterHdr hparse)
    (hblockEnd2 hdr afterHdr hparse) hlit2' hseq2'
  -- Step 4: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-! ## decompressZstd two-block composed completeness (raw first block) -/

/-- End-to-end composed completeness for a frame with two raw blocks:
    byte-level conditions on the frame header and both block headers imply
    `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_two_raw_blocks` (header + two raw blocks → frame success)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_two_raw_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zstd.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block 1 (non-last raw) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last raw) at off2 = afterHdr + 3 + block1Size
    (hsize2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ¬ (hdr.windowSize > 0 &&
            ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
              ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 3 +
            (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
              ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Frame terminates the data
    (hterm : ∀ content pos', Zstd.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zstd.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Apply decompressFrame_succeeds_two_raw_blocks
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_two_raw_blocks
    data 0 hdr afterHdr hparse
    (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse) (hnosize hdr afterHdr hparse)
    (hsize1 hdr afterHdr hparse) (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse) (hpayload1 hdr afterHdr hparse)
    rfl (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse) (hlastBit2 hdr afterHdr hparse)
    (hblockSize2 hdr afterHdr hparse) (hwindow2 hdr afterHdr hparse) (hpayload2 hdr afterHdr hparse)
  -- Step 3: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-- End-to-end composed completeness for a frame with a raw first block and RLE
    second block: byte-level conditions on the frame header and both block headers
    imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_raw_then_rle` (header + raw + RLE blocks → frame success)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_raw_then_rle_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zstd.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block 1 (non-last raw) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last RLE) at off2 = afterHdr + 3 + block1Size
    (hsize2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ¬ (hdr.windowSize > 0 &&
            ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
              ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 4)
    -- Frame terminates the data
    (hterm : ∀ content pos', Zstd.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zstd.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Apply decompressFrame_succeeds_raw_then_rle
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_raw_then_rle
    data 0 hdr afterHdr hparse
    (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse) (hnosize hdr afterHdr hparse)
    (hsize1 hdr afterHdr hparse) (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse) (hpayload1 hdr afterHdr hparse)
    _ rfl (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse)
    (hlastBit2 hdr afterHdr hparse) (hblockSize2 hdr afterHdr hparse)
    (hwindow2 hdr afterHdr hparse) (hpayload2 hdr afterHdr hparse)
  -- Step 3: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-- End-to-end composed completeness for a frame with a raw first block and
    compressed second block (zero sequences): byte-level conditions on the frame
    header, both block headers, and parsing conditions imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_raw_then_compressed_zero_seq` (header + raw + compressed → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_raw_then_compressed_zero_seq_frame (data : ByteArray)
    -- Frame header conditions (from parseFrameHeader_succeeds)
    (hmagic : Binary.readUInt32LE data 0 = Zstd.Native.zstdMagic)
    (hframeSize : data.size ≥ Zstd.Spec.frameHeaderMinSize data[4]!)
    -- Header field constraints (universally quantified over parseFrameHeader result)
    (hnodict : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.dictionaryId = none)
    (hnocksum : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentChecksum = false)
    (hnosize : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → hdr.contentSize = none)
    -- Block 1 (non-last raw) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hpayload1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last compressed, zero sequences) at off2 = afterHdr + 3 + block1Size
    (hsize2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
    (hlastBit2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
            ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ¬ (hdr.windowSize > 0 &&
            ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
              ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > hdr.windowSize))
    (hblockEnd2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        data.size ≥ off2 + 3 +
            (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
              ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Literals section and sequences header succeed at block 2 (quantified, with existentials)
    (hparsing2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ∃ literals afterLiterals huffTree modes afterSeqHeader,
            Zstd.Native.parseLiteralsSection data (off2 + 3) none
              = .ok (literals, afterLiterals, huffTree) ∧
            Zstd.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader))
    -- Frame terminates the data
    (hterm : ∀ content pos', Zstd.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zstd.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Obtain literals and sequences parsing from combined hypothesis
  obtain ⟨literals, afterLiterals, huffTree, modes, afterSeqHeader, hlit', hseq'⟩ :=
    hparsing2 hdr afterHdr hparse
  -- Step 3: Apply decompressFrame_succeeds_raw_then_compressed_zero_seq
  obtain ⟨content, pos', hframe⟩ :=
    Zstd.Spec.decompressFrame_succeeds_raw_then_compressed_zero_seq
    data 0 hdr afterHdr literals afterLiterals huffTree modes afterSeqHeader
    hparse (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
    (hnosize hdr afterHdr hparse)
    (hsize1 hdr afterHdr hparse) (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse) (hpayload1 hdr afterHdr hparse)
    _ rfl (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse)
    (hlastBit2 hdr afterHdr hparse) (hblockSize2 hdr afterHdr hparse)
    (hwindow2 hdr afterHdr hparse) (hblockEnd2 hdr afterHdr hparse) hlit' hseq'
  -- Step 4: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-! ## decompressZstd two-block composed completeness (raw/RLE first, compressed-sequences second) -/

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (first non-last raw, second last compressed with numSeq>0), `decompressZstd`
    succeeds.  Derived from `decompressZstd_raw_then_compressed_seq_content`. -/
theorem decompressZstd_succeeds_raw_then_compressed_sequences_frame (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last raw)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterBlock1 : Nat)
    -- Block 2 (last compressed, numSeq > 0)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zstd.Native.ZstdHuffmanTable)
    (numSeq2 : Nat) (modes2 : Zstd.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
    (llTable2 ofTable2 mlTable2 : Zstd.Native.FseTable) (afterTables2 : Nat)
    (bbr2 : Zstd.Native.BackwardBitReader)
    (sequences2 : Array Zstd.Native.ZstdSequence)
    (blockOutput2 : ByteArray) (newHist2 : Array Nat)
    -- Frame hypotheses
    (hframe : Zstd.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zstd.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    -- Block 1 hypotheses (raw, non-last)
    (hparse1 : Zstd.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .raw)
    (hraw1 : Zstd.Native.decompressRawBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterBlock1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterBlock1 ≤ afterHeader)
    -- Block 2 hypotheses (compressed, last, numSeq > 0)
    (hoff2 : ¬ data.size ≤ afterBlock1)
    (hparse2 : Zstd.Native.parseBlockHeader data afterBlock1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zstd.Native.parseLiteralsSection data afterHdr2 none
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zstd.Native.parseSequencesHeader data afterLiterals2
               = .ok (numSeq2, modes2, afterSeqHeader2))
    (hNumSeq2 : ¬ numSeq2 == 0)
    (hfse2 : Zstd.Native.resolveSequenceFseTables modes2 data afterSeqHeader2 {}
               = .ok (llTable2, ofTable2, mlTable2, afterTables2))
    (hbbr2 : Zstd.Native.BackwardBitReader.init data afterTables2
               (afterHdr2 + hdr2.blockSize.toNat) = .ok bbr2)
    (hdec2 : Zstd.Native.decodeSequences llTable2 ofTable2 mlTable2 bbr2 numSeq2
               = .ok sequences2)
    (hexec2 : Zstd.Native.executeSequences sequences2 literals2
                (if header.windowSize > 0 && block1.size > header.windowSize.toNat
                 then block1.extract (block1.size - header.windowSize.toNat) block1.size
                 else block1)
                #[1, 4, 8] header.windowSize.toNat
                = .ok (blockOutput2, newHist2))
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    ∃ out, Zstd.Native.decompressZstd data = .ok out :=
  ⟨_, decompressZstd_raw_then_compressed_seq_content data output pos'
    header afterHeader hdr1 afterHdr1 block1 afterBlock1
    hdr2 afterHdr2 literals2 afterLiterals2 huffTree2
    numSeq2 modes2 afterSeqHeader2 llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2
    blockOutput2 newHist2
    hframe hh hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hNumSeq2
    hfse2 hbbr2 hdec2 hexec2 hlast2 hend⟩

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (first non-last RLE, second last compressed with numSeq>0), `decompressZstd`
    succeeds.  Derived from `decompressZstd_rle_then_compressed_seq_content`. -/
theorem decompressZstd_succeeds_rle_then_compressed_sequences_frame (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last RLE)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterByte1 : Nat)
    -- Block 2 (last compressed, numSeq > 0)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zstd.Native.ZstdHuffmanTable)
    (numSeq2 : Nat) (modes2 : Zstd.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
    (llTable2 ofTable2 mlTable2 : Zstd.Native.FseTable) (afterTables2 : Nat)
    (bbr2 : Zstd.Native.BackwardBitReader)
    (sequences2 : Array Zstd.Native.ZstdSequence)
    (blockOutput2 : ByteArray) (newHist2 : Array Nat)
    -- Frame hypotheses
    (hframe : Zstd.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zstd.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
    -- Block 1 hypotheses (RLE, non-last)
    (hparse1 : Zstd.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .rle)
    (hrle1 : Zstd.Native.decompressRLEBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterByte1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterByte1 ≤ afterHeader)
    -- Block 2 hypotheses (compressed, last, numSeq > 0)
    (hoff2 : ¬ data.size ≤ afterByte1)
    (hparse2 : Zstd.Native.parseBlockHeader data afterByte1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zstd.Native.parseLiteralsSection data afterHdr2 none
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zstd.Native.parseSequencesHeader data afterLiterals2
               = .ok (numSeq2, modes2, afterSeqHeader2))
    (hNumSeq2 : ¬ numSeq2 == 0)
    (hfse2 : Zstd.Native.resolveSequenceFseTables modes2 data afterSeqHeader2 {}
               = .ok (llTable2, ofTable2, mlTable2, afterTables2))
    (hbbr2 : Zstd.Native.BackwardBitReader.init data afterTables2
               (afterHdr2 + hdr2.blockSize.toNat) = .ok bbr2)
    (hdec2 : Zstd.Native.decodeSequences llTable2 ofTable2 mlTable2 bbr2 numSeq2
               = .ok sequences2)
    (hexec2 : Zstd.Native.executeSequences sequences2 literals2
                (if header.windowSize > 0 && block1.size > header.windowSize.toNat
                 then block1.extract (block1.size - header.windowSize.toNat) block1.size
                 else block1)
                #[1, 4, 8] header.windowSize.toNat
                = .ok (blockOutput2, newHist2))
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    ∃ out, Zstd.Native.decompressZstd data = .ok out :=
  ⟨_, decompressZstd_rle_then_compressed_seq_content data output pos'
    header afterHeader hdr1 afterHdr1 block1 afterByte1
    hdr2 afterHdr2 literals2 afterLiterals2 huffTree2
    numSeq2 modes2 afterSeqHeader2 llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2
    blockOutput2 newHist2
    hframe hh hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hNumSeq2
    hfse2 hbbr2 hdec2 hexec2 hlast2 hend⟩

end Zstd.Spec.ZstdFrame
