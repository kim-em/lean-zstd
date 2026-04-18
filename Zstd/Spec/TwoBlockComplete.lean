import Zstd.Spec.TwoBlockBase

/-!
# Zstandard Two-Block Complete Spec

Composed completeness theorems for two-block frames:
- `decompressFrame` succeeds for two raw/RLE blocks (homogeneous)
- `decompressFrame` succeeds for mixed raw/RLE block sequences (heterogeneous)
- Frame-level position advancement (`decompressFrame_pos_gt`, `_le_size`)
- Frame-level content characterization for single and two-block raw/RLE frames
-/

-- Frame-level proof helper: unfolds `decompressFrame`, substitutes `hh` and
-- `hblocks`, handles the dictionary check, and closes both branches with grind.
-- Duplicated from ZstdBase.lean because `local macro` is file-scoped.
set_option hygiene false in
local macro "frame_from_blocks" : tactic =>
  `(tactic| (
    unfold Zstd.Native.decompressFrame at hframe
    dsimp only [Bind.bind, Except.bind] at hframe
    rw [hh] at hframe
    simp only [pure, Except.pure] at hframe
    split at hframe
    · split at hframe
      · exact nomatch hframe
      · unfold Zstd.Native.decompressBlocks at hframe
        rw [hblocks] at hframe
        simp only [ByteArray.empty_append] at hframe
        grind
    · unfold Zstd.Native.decompressBlocks at hframe
      rw [hblocks] at hframe
      simp only [ByteArray.empty_append] at hframe
      grind))

namespace Zstd.Spec

/-! ## decompressFrame two-block composed completeness (homogeneous) -/

/-- When a frame contains two consecutive raw blocks (first non-last, second last),
    with no dictionary, no content checksum, and no declared content size,
    `decompressFrame` succeeds. Composes `parseFrameHeader` success with
    `decompressBlocksWF_succeeds_two_raw_blocks` and threads through the
    frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_two_raw_blocks (data : ByteArray) (pos : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hparse : Zstd.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    -- Block 1 byte-level conditions (non-last raw at afterHeader)
    (hsize1 : data.size ≥ afterHeader + 3)
    (htypeVal1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit1 : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload1 : data.size ≥ afterHeader + 3 +
        (((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 position and byte-level conditions (last raw)
    {off2 : Nat}
    (hoff2 : off2 = afterHeader + 3 +
        (((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (header.windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) :
    ∃ content pos',
      Zstd.Native.decompressFrame data pos = .ok (content, pos') :=
  decompressFrame_of_blocks_succeed data pos header afterHeader hparse hnodict hnocksum hnosize
    (decompressBlocksWF_succeeds_two_raw_blocks data afterHeader off2 header.windowSize
      ByteArray.empty none {} #[1, 4, 8]
      hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hpayload1 hoff2
      hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2)

/-- When a frame contains two consecutive RLE blocks (first non-last, second last),
    with no dictionary, no content checksum, and no declared content size,
    `decompressFrame` succeeds. Composes `parseFrameHeader` success with
    `decompressBlocksWF_succeeds_two_rle_blocks` and threads through the
    frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_two_rle_blocks (data : ByteArray) (pos : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hparse : Zstd.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    -- Block 1 byte-level conditions (non-last RLE at afterHeader)
    (hsize1 : data.size ≥ afterHeader + 3)
    (htypeVal1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit1 : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload1 : data.size ≥ afterHeader + 4)
    -- Block 2 position and byte-level conditions (last RLE)
    {off2 : Nat}
    (hoff2 : off2 = afterHeader + 4)
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (header.windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload2 : data.size ≥ off2 + 4) :
    ∃ content pos',
      Zstd.Native.decompressFrame data pos = .ok (content, pos') :=
  decompressFrame_of_blocks_succeed data pos header afterHeader hparse hnodict hnocksum hnosize
    (decompressBlocksWF_succeeds_two_rle_blocks data afterHeader off2 header.windowSize
      ByteArray.empty none {} #[1, 4, 8]
      hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hpayload1 hoff2
      hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2)
/-! ## decompressFrame two-block composed completeness (heterogeneous) -/

/-- When a frame contains a non-last raw block followed by a last RLE block,
    with no dictionary, no content checksum, and no declared content size,
    `decompressFrame` succeeds. This composes `parseFrameHeader` success with
    `decompressBlocksWF_succeeds_raw_then_rle` and threads through the
    frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_raw_then_rle (data : ByteArray) (pos : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hparse : Zstd.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    -- Block 1 (non-last raw) at afterHeader
    (hsize1 : data.size ≥ afterHeader + 3)
    (htypeVal1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit1 : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload1 : data.size ≥ afterHeader + 3 +
        (((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last RLE) at off2
    (off2 : Nat)
    (hoff2 : off2 = afterHeader + 3 + (((data[afterHeader]!.toUInt32
          ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (header.windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload2 : data.size ≥ off2 + 4) :
    ∃ content pos',
      Zstd.Native.decompressFrame data pos = .ok (content, pos') :=
  decompressFrame_of_blocks_succeed data pos header afterHeader hparse hnodict hnocksum hnosize
    (decompressBlocksWF_succeeds_raw_then_rle data afterHeader off2 header.windowSize
      ByteArray.empty none {} #[1, 4, 8]
      hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hpayload1 hoff2
      hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2)

/-- When a frame contains a non-last RLE block followed by a last raw block,
    with no dictionary, no content checksum, and no declared content size,
    `decompressFrame` succeeds. This composes `parseFrameHeader` success with
    `decompressBlocksWF_succeeds_rle_then_raw` and threads through the
    frame-level dictionary/checksum/size guards. -/
theorem decompressFrame_succeeds_rle_then_raw (data : ByteArray) (pos : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hparse : Zstd.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    -- Block 1 (non-last RLE) at afterHeader
    (hsize1 : data.size ≥ afterHeader + 3)
    (htypeVal1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit1 : (data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
        ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (header.windowSize > 0 &&
        ((data[afterHeader]!.toUInt32 ||| (data[afterHeader + 1]!.toUInt32 <<< 8)
          ||| (data[afterHeader + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload1 : data.size ≥ afterHeader + 4)
    -- Block 2 (last raw) at off2
    (off2 : Nat)
    (hoff2 : off2 = afterHeader + 4)
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (header.windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > header.windowSize))
    (hpayload2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) :
    ∃ content pos',
      Zstd.Native.decompressFrame data pos = .ok (content, pos') :=
  decompressFrame_of_blocks_succeed data pos header afterHeader hparse hnodict hnocksum hnosize
    (decompressBlocksWF_succeeds_rle_then_raw data afterHeader off2 header.windowSize
      ByteArray.empty none {} #[1, 4, 8]
      hsize1 htypeVal1 hlastBit1 hblockSize1 hwindow1 hpayload1 hoff2
      hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2)
/-! ## Frame-level position advancement -/

/-- When `decompressFrame` succeeds, the returned position is strictly greater
    than the input position. This follows from `parseFrameHeader_pos_gt`
    (header ≥ 6 bytes) and `decompressBlocksWF_pos_gt` (blocks ≥ 3 bytes),
    plus an optional 4-byte checksum. -/
theorem decompressFrame_pos_gt (data : ByteArray) (pos : Nat)
    (output : ByteArray) (pos' : Nat)
    (h : Zstd.Native.decompressFrame data pos = .ok (output, pos')) :
    pos' > pos := by
  unfold Zstd.Native.decompressFrame at h
  cases hph : Zstd.Native.parseFrameHeader data pos with
  | error e => simp only [hph, bind, Except.bind] at h; exact nomatch h
  | ok val =>
    obtain ⟨header, afterHeader⟩ := val
    have hgt1 := parseFrameHeader_pos_gt _ _ _ _ hph
    simp only [hph, bind, Except.bind, pure, Except.pure] at h
    -- Dictionary check: close the dictId != 0 error branch, then handle both paths uniformly
    split at h
    · split at h
      · exact nomatch h
      · unfold Zstd.Native.decompressBlocks at h
        cases hdb : Zstd.Native.decompressBlocksWF data afterHeader header.windowSize
            ByteArray.empty none {} #[1, 4, 8] with
        | error e => simp only [hdb] at h; exact nomatch h
        | ok val2 =>
          obtain ⟨content, afterBlocks⟩ := val2
          have hgt2 := decompressBlocksWF_pos_gt _ _ _ _ _ _ _ _ _ hdb
          simp only [hdb] at h; grind
    · unfold Zstd.Native.decompressBlocks at h
      cases hdb : Zstd.Native.decompressBlocksWF data afterHeader header.windowSize
          ByteArray.empty none {} #[1, 4, 8] with
      | error e => simp only [hdb] at h; exact nomatch h
      | ok val2 =>
        obtain ⟨content, afterBlocks⟩ := val2
        have hgt2 := decompressBlocksWF_pos_gt _ _ _ _ _ _ _ _ _ hdb
        simp only [hdb] at h; grind

/-- When `decompressFrame` succeeds, the returned position is within data bounds.
    This is the frame-level capstone of the le_size campaign: it composes
    `decompressBlocksWF_le_size` with the checksum bounds guard. -/
theorem decompressFrame_le_size (data : ByteArray) (pos : Nat)
    (output : ByteArray) (pos' : Nat)
    (h : Zstd.Native.decompressFrame data pos = .ok (output, pos')) :
    pos' ≤ data.size := by
  unfold Zstd.Native.decompressFrame at h
  cases hph : Zstd.Native.parseFrameHeader data pos with
  | error e => simp only [hph, bind, Except.bind] at h; exact nomatch h
  | ok val =>
    obtain ⟨header, afterHeader⟩ := val
    simp only [hph, bind, Except.bind, pure, Except.pure] at h
    split at h
    · split at h
      · exact nomatch h
      · unfold Zstd.Native.decompressBlocks at h
        cases hdb : Zstd.Native.decompressBlocksWF data afterHeader header.windowSize
            ByteArray.empty none {} #[1, 4, 8] with
        | error e => simp only [hdb] at h; exact nomatch h
        | ok val2 =>
          obtain ⟨content, afterBlocks⟩ := val2
          have hle := decompressBlocksWF_le_size _ _ _ _ _ _ _ _ _ hdb
          simp only [hdb] at h; grind
    · unfold Zstd.Native.decompressBlocks at h
      cases hdb : Zstd.Native.decompressBlocksWF data afterHeader header.windowSize
          ByteArray.empty none {} #[1, 4, 8] with
      | error e => simp only [hdb] at h; exact nomatch h
      | ok val2 =>
        obtain ⟨content, afterBlocks⟩ := val2
        have hle := decompressBlocksWF_le_size _ _ _ _ _ _ _ _ _ hdb
        simp only [hdb] at h; grind

/-! ## Frame-level content characterization -/

/-- When `decompressFrame` succeeds and the frame contains a single raw last block,
    the output equals the raw block content. Composes `decompressBlocksWF_single_raw`
    with the frame-level dictionary check, checksum, and content size validation. -/
theorem decompressFrame_single_raw_content (data : ByteArray) (pos : Nat)
    (output : ByteArray) (pos' : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hdr : Zstd.Native.ZstdBlockHeader) (afterHdr : Nat)
    (block : ByteArray) (afterBlock : Nat)
    (hframe : Zstd.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zstd.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hparse : Zstd.Native.parseBlockHeader data afterHeader = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (header.windowSize > 0 && hdr.blockSize.toUInt64 > header.windowSize))
    (htype : hdr.blockType = .raw)
    (hraw : Zstd.Native.decompressRawBlock data afterHdr hdr.blockSize = .ok (block, afterBlock))
    (hlast : hdr.lastBlock = true) :
    output = block := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr afterHdr hparse
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_single_raw data afterHeader header.windowSize
    ByteArray.empty none {} #[1, 4, 8] hdr afterHdr block afterBlock
    hoff hparse hbs hws htype hraw hlast
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a single RLE last block,
    the output equals the RLE block content. Composes `decompressBlocksWF_single_rle`
    with the frame-level dictionary check, checksum, and content size validation. -/
theorem decompressFrame_single_rle_content (data : ByteArray) (pos : Nat)
    (output : ByteArray) (pos' : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hdr : Zstd.Native.ZstdBlockHeader) (afterHdr : Nat)
    (block : ByteArray) (afterByte : Nat)
    (hframe : Zstd.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zstd.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hparse : Zstd.Native.parseBlockHeader data afterHeader = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (header.windowSize > 0 && hdr.blockSize.toUInt64 > header.windowSize))
    (htype : hdr.blockType = .rle)
    (hrle : Zstd.Native.decompressRLEBlock data afterHdr hdr.blockSize = .ok (block, afterByte))
    (hlast : hdr.lastBlock = true) :
    output = block := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr afterHdr hparse
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_single_rle data afterHeader header.windowSize
    ByteArray.empty none {} #[1, 4, 8] hdr afterHdr block afterByte
    hoff hparse hbs hws htype hrle hlast
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains two consecutive raw blocks
    (first non-last, second last), the output equals `block1 ++ block2`.
    Composes `decompressBlocksWF_two_raw_blocks` with the frame-level dictionary check,
    checksum, and content size validation. -/
theorem decompressFrame_two_raw_blocks_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last raw)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterBlock1 : Nat)
    -- Block 2 (last raw)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterBlock2 : Nat)
    -- Frame hypotheses
    (hframe : Zstd.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zstd.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    -- Block 1 hypotheses
    (hparse1 : Zstd.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .raw)
    (hraw1 : Zstd.Native.decompressRawBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterBlock1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterBlock1 ≤ afterHeader)
    -- Block 2 hypotheses
    (hoff2 : ¬ data.size ≤ afterBlock1)
    (hparse2 : Zstd.Native.parseBlockHeader data afterBlock1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .raw)
    (hraw2 : Zstd.Native.decompressRawBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterBlock2))
    (hlast2 : hdr2.lastBlock = true) :
    output = block1 ++ block2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_two_raw_blocks data afterHeader header.windowSize
    ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1 block1 afterBlock1
    hdr2 afterHdr2 block2 afterBlock2
    hoff hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hraw2 hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains two consecutive RLE blocks
    (first non-last, second last), the output equals `block1 ++ block2`.
    Composes `decompressBlocksWF_two_rle_blocks` with the frame-level dictionary check,
    checksum, and content size validation. -/
theorem decompressFrame_two_rle_blocks_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last RLE)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterByte1 : Nat)
    -- Block 2 (last RLE)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterByte2 : Nat)
    -- Frame hypotheses
    (hframe : Zstd.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zstd.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    -- Block 1 hypotheses
    (hparse1 : Zstd.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .rle)
    (hrle1 : Zstd.Native.decompressRLEBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterByte1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterByte1 ≤ afterHeader)
    -- Block 2 hypotheses
    (hoff2 : ¬ data.size ≤ afterByte1)
    (hparse2 : Zstd.Native.parseBlockHeader data afterByte1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .rle)
    (hrle2 : Zstd.Native.decompressRLEBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterByte2))
    (hlast2 : hdr2.lastBlock = true) :
    output = block1 ++ block2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_two_rle_blocks data afterHeader header.windowSize
    ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1 block1 afterByte1
    hdr2 afterHdr2 block2 afterByte2
    hoff hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hrle2 hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a non-last raw block
    followed by a last RLE block, the output equals `block1 ++ block2`.
    Composes `decompressBlocksWF_raw_then_rle` with the frame-level dictionary check,
    checksum, and content size validation. -/
theorem decompressFrame_raw_then_rle_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last raw)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterBlock1 : Nat)
    -- Block 2 (last RLE)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterByte2 : Nat)
    -- Frame hypotheses
    (hframe : Zstd.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zstd.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    -- Block 1 hypotheses (raw, non-last)
    (hparse1 : Zstd.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .raw)
    (hraw1 : Zstd.Native.decompressRawBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterBlock1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterBlock1 ≤ afterHeader)
    -- Block 2 hypotheses (RLE, last)
    (hoff2 : ¬ data.size ≤ afterBlock1)
    (hparse2 : Zstd.Native.parseBlockHeader data afterBlock1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .rle)
    (hrle2 : Zstd.Native.decompressRLEBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterByte2))
    (hlast2 : hdr2.lastBlock = true) :
    output = block1 ++ block2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_raw_then_rle data afterHeader header.windowSize
    ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1 block1 afterBlock1
    hdr2 afterHdr2 block2 afterByte2
    hoff hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hrle2 hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a non-last RLE block
    followed by a last raw block, the output equals `block1 ++ block2`.
    Composes `decompressBlocksWF_rle_then_raw` with the frame-level dictionary check,
    checksum, and content size validation. -/
theorem decompressFrame_rle_then_raw_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last RLE)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterByte1 : Nat)
    -- Block 2 (last raw)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterBlock2 : Nat)
    -- Frame hypotheses
    (hframe : Zstd.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zstd.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    -- Block 1 hypotheses (RLE, non-last)
    (hparse1 : Zstd.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .rle)
    (hrle1 : Zstd.Native.decompressRLEBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterByte1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterByte1 ≤ afterHeader)
    -- Block 2 hypotheses (raw, last)
    (hoff2 : ¬ data.size ≤ afterByte1)
    (hparse2 : Zstd.Native.parseBlockHeader data afterByte1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .raw)
    (hraw2 : Zstd.Native.decompressRawBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterBlock2))
    (hlast2 : hdr2.lastBlock = true) :
    output = block1 ++ block2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_rle_then_raw data afterHeader header.windowSize
    ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1 block1 afterByte1
    hdr2 afterHdr2 block2 afterBlock2
    hoff hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hraw2 hlast2
  frame_from_blocks

end Zstd.Spec
