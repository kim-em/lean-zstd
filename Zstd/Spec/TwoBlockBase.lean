import Zstd.Spec.BlockLoop

/-!
# Zstandard Two-Block Base Spec

Shared setup lemmas, structural composition theorems, and frame header
machinery used by the two-block Zstd specifications.

Sections:
- Step theorems for raw and RLE blocks
- `WellFormedSimpleBlocks` induction predicate for raw/RLE-only sequences
- Homogeneous two-block composition and block-level completeness (raw, RLE)
- Frame-level wrapping helper
- Heterogeneous raw/RLE composition and block-level completeness
- `parseFrameHeader` position advancement and field characterization
- `windowSizeFromDescriptor` bounds

Block-level completeness theorems involving compressed blocks are in
`Zstd.Spec.TwoBlockCompressed`. Frame-level completeness and content
characterization are in `Zstd.Spec.TwoBlockComplete`.
-/

namespace Zstd.Spec

/-! ## decompressBlocksWF step theorems -/

/-- When `decompressBlocksWF` encounters a non-last raw block, it recurses with
    `output ++ block` and position `afterBlock`. The Huffman table, FSE tables,
    and offset history are unchanged (raw blocks don't update them). -/
theorem decompressBlocksWF_raw_step (data : ByteArray) (off : Nat)
    (windowSize : UInt64) (output : ByteArray) (prevHuff : Option Zstd.Native.ZstdHuffmanTable)
    (prevFse : Zstd.Native.PrevFseTables) (history : Array Nat)
    (hdr : Zstd.Native.ZstdBlockHeader) (afterHdr : Nat)
    (block : ByteArray) (afterBlock : Nat)
    (hoff : ¬ data.size ≤ off)
    (hparse : Zstd.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
    (htype : hdr.blockType = .raw)
    (hraw : Zstd.Native.decompressRawBlock data afterHdr hdr.blockSize = .ok (block, afterBlock))
    (hnotlast : hdr.lastBlock = false)
    (hadv : ¬ afterBlock ≤ off) :
    Zstd.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = Zstd.Native.decompressBlocksWF data afterBlock windowSize (output ++ block)
          prevHuff prevFse history := by
  generalize heq : Zstd.Native.decompressBlocksWF data afterBlock windowSize
    (output ++ block) prevHuff prevFse history = rhs
  unfold Zstd.Native.decompressBlocksWF
  simp only [hoff, ↓reduceDIte, hparse, hbs, hws, htype, hraw, hnotlast, hadv,
    bind, Except.bind, pure, Except.pure, ↓reduceIte, Bool.false_eq_true]
  exact heq

/-- When `decompressBlocksWF` encounters a non-last RLE block, it recurses with
    `output ++ block` and position `afterByte`. The Huffman table, FSE tables,
    and offset history are unchanged (RLE blocks don't update them). -/
theorem decompressBlocksWF_rle_step (data : ByteArray) (off : Nat)
    (windowSize : UInt64) (output : ByteArray) (prevHuff : Option Zstd.Native.ZstdHuffmanTable)
    (prevFse : Zstd.Native.PrevFseTables) (history : Array Nat)
    (hdr : Zstd.Native.ZstdBlockHeader) (afterHdr : Nat)
    (block : ByteArray) (afterByte : Nat)
    (hoff : ¬ data.size ≤ off)
    (hparse : Zstd.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
    (htype : hdr.blockType = .rle)
    (hrle : Zstd.Native.decompressRLEBlock data afterHdr hdr.blockSize = .ok (block, afterByte))
    (hnotlast : hdr.lastBlock = false)
    (hadv : ¬ afterByte ≤ off) :
    Zstd.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = Zstd.Native.decompressBlocksWF data afterByte windowSize (output ++ block)
          prevHuff prevFse history := by
  generalize heq : Zstd.Native.decompressBlocksWF data afterByte windowSize
    (output ++ block) prevHuff prevFse history = rhs
  unfold Zstd.Native.decompressBlocksWF
  simp only [hoff, ↓reduceDIte, hparse, hbs, hws, htype, hrle, hnotlast, hadv,
    bind, Except.bind, pure, Except.pure, ↓reduceIte, Bool.false_eq_true]
  exact heq

/-! ## WellFormedSimpleBlocks induction predicate -/

/-- An inductive predicate encoding a sequence of raw/RLE blocks, each satisfying
    the hypotheses of the existing step/base theorems. Raw and RLE blocks don't
    update Huffman tables, FSE tables, or offset history, so the recursive calls
    use the same `prevHuff`, `prevFse`, `history`. -/
inductive WellFormedSimpleBlocks (data : ByteArray) :
    Nat → UInt64 → ByteArray →
    Option Zstd.Native.ZstdHuffmanTable →
    Zstd.Native.PrevFseTables → Array Nat → Prop where
  | last_raw (off windowSize output prevHuff prevFse history
      hdr afterHdr block afterBlock :_)
      (hoff : ¬ data.size ≤ off)
      (hparse : Zstd.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
      (hbs : ¬ hdr.blockSize > 131072)
      (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
      (htype : hdr.blockType = .raw)
      (hraw : Zstd.Native.decompressRawBlock data afterHdr hdr.blockSize = .ok (block, afterBlock))
      (hlast : hdr.lastBlock = true) :
      WellFormedSimpleBlocks data off windowSize output prevHuff prevFse history
  | last_rle (off windowSize output prevHuff prevFse history
      hdr afterHdr block afterByte :_)
      (hoff : ¬ data.size ≤ off)
      (hparse : Zstd.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
      (hbs : ¬ hdr.blockSize > 131072)
      (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
      (htype : hdr.blockType = .rle)
      (hrle : Zstd.Native.decompressRLEBlock data afterHdr hdr.blockSize = .ok (block, afterByte))
      (hlast : hdr.lastBlock = true) :
      WellFormedSimpleBlocks data off windowSize output prevHuff prevFse history
  | step_raw (off windowSize output prevHuff prevFse history
      hdr afterHdr block afterBlock :_)
      (hoff : ¬ data.size ≤ off)
      (hparse : Zstd.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
      (hbs : ¬ hdr.blockSize > 131072)
      (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
      (htype : hdr.blockType = .raw)
      (hraw : Zstd.Native.decompressRawBlock data afterHdr hdr.blockSize = .ok (block, afterBlock))
      (hnotlast : hdr.lastBlock = false)
      (hadv : ¬ afterBlock ≤ off)
      (rest : WellFormedSimpleBlocks data afterBlock windowSize
        (output ++ block) prevHuff prevFse history) :
      WellFormedSimpleBlocks data off windowSize output prevHuff prevFse history
  | step_rle (off windowSize output prevHuff prevFse history
      hdr afterHdr block afterByte :_)
      (hoff : ¬ data.size ≤ off)
      (hparse : Zstd.Native.parseBlockHeader data off = .ok (hdr, afterHdr))
      (hbs : ¬ hdr.blockSize > 131072)
      (hws : ¬ (windowSize > 0 && hdr.blockSize.toUInt64 > windowSize))
      (htype : hdr.blockType = .rle)
      (hrle : Zstd.Native.decompressRLEBlock data afterHdr hdr.blockSize = .ok (block, afterByte))
      (hnotlast : hdr.lastBlock = false)
      (hadv : ¬ afterByte ≤ off)
      (rest : WellFormedSimpleBlocks data afterByte windowSize
        (output ++ block) prevHuff prevFse history) :
      WellFormedSimpleBlocks data off windowSize output prevHuff prevFse history

/-- `decompressBlocksWF` succeeds on any well-formed sequence of raw/RLE blocks.
    This subsumes all specific N-block raw/RLE completeness theorems. -/
theorem decompressBlocksWF_succeeds_of_well_formed_simple
    (data : ByteArray) (off : Nat) (windowSize : UInt64)
    (output : ByteArray) (prevHuff : Option Zstd.Native.ZstdHuffmanTable)
    (prevFse : Zstd.Native.PrevFseTables) (history : Array Nat)
    (hwf : WellFormedSimpleBlocks data off windowSize output prevHuff prevFse history) :
    ∃ result pos',
      Zstd.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  induction hwf with
  | last_raw off windowSize output prevHuff prevFse history
      hdr afterHdr block afterBlock hoff hparse hbs hws htype hraw hlast =>
    exact ⟨_, _, decompressBlocksWF_single_raw data off windowSize output prevHuff prevFse
      history hdr afterHdr block afterBlock hoff hparse hbs hws htype hraw hlast⟩
  | last_rle off windowSize output prevHuff prevFse history
      hdr afterHdr block afterByte hoff hparse hbs hws htype hrle hlast =>
    exact ⟨_, _, decompressBlocksWF_single_rle data off windowSize output prevHuff prevFse
      history hdr afterHdr block afterByte hoff hparse hbs hws htype hrle hlast⟩
  | step_raw off windowSize output prevHuff prevFse history
      hdr afterHdr block afterBlock hoff hparse hbs hws htype hraw hnotlast hadv _rest ih =>
    rw [decompressBlocksWF_raw_step data off windowSize output prevHuff prevFse history
      hdr afterHdr block afterBlock hoff hparse hbs hws htype hraw hnotlast hadv]
    exact ih
  | step_rle off windowSize output prevHuff prevFse history
      hdr afterHdr block afterByte hoff hparse hbs hws htype hrle hnotlast hadv _rest ih =>
    rw [decompressBlocksWF_rle_step data off windowSize output prevHuff prevFse history
      hdr afterHdr block afterByte hoff hparse hbs hws htype hrle hnotlast hadv]
    exact ih

/-- Three consecutive raw blocks (two non-last, one last) succeed. Demonstrates that
    N-block completeness is a trivial corollary of `WellFormedSimpleBlocks` induction:
    construct the chain and apply the theorem. -/
theorem decompressBlocksWF_succeeds_three_raw
    (data : ByteArray) (off : Nat) (windowSize : UInt64)
    (output : ByteArray) (prevHuff : Option Zstd.Native.ZstdHuffmanTable)
    (prevFse : Zstd.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last raw)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterBlock1 : Nat)
    (hoff1 : ¬ data.size ≤ off)
    (hparse1 : Zstd.Native.parseBlockHeader data off = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize))
    (htype1 : hdr1.blockType = .raw)
    (hraw1 : Zstd.Native.decompressRawBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterBlock1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterBlock1 ≤ off)
    -- Block 2 (non-last raw)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterBlock2 : Nat)
    (hoff2 : ¬ data.size ≤ afterBlock1)
    (hparse2 : Zstd.Native.parseBlockHeader data afterBlock1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (windowSize > 0 && hdr2.blockSize.toUInt64 > windowSize))
    (htype2 : hdr2.blockType = .raw)
    (hraw2 : Zstd.Native.decompressRawBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterBlock2))
    (hnotlast2 : hdr2.lastBlock = false)
    (hadv2 : ¬ afterBlock2 ≤ afterBlock1)
    -- Block 3 (last raw)
    (hdr3 : Zstd.Native.ZstdBlockHeader) (afterHdr3 : Nat)
    (block3 : ByteArray) (afterBlock3 : Nat)
    (hoff3 : ¬ data.size ≤ afterBlock2)
    (hparse3 : Zstd.Native.parseBlockHeader data afterBlock2 = .ok (hdr3, afterHdr3))
    (hbs3 : ¬ hdr3.blockSize > 131072)
    (hws3 : ¬ (windowSize > 0 && hdr3.blockSize.toUInt64 > windowSize))
    (htype3 : hdr3.blockType = .raw)
    (hraw3 : Zstd.Native.decompressRawBlock data afterHdr3 hdr3.blockSize
               = .ok (block3, afterBlock3))
    (hlast3 : hdr3.lastBlock = true) :
    ∃ result pos',
      Zstd.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') :=
  decompressBlocksWF_succeeds_of_well_formed_simple data off windowSize output
    prevHuff prevFse history
    (.step_raw off windowSize output prevHuff prevFse history
      hdr1 afterHdr1 block1 afterBlock1
      hoff1 hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1
      (.step_raw afterBlock1 windowSize (output ++ block1) prevHuff prevFse history
        hdr2 afterHdr2 block2 afterBlock2
        hoff2 hparse2 hbs2 hws2 htype2 hraw2 hnotlast2 hadv2
        (.last_raw afterBlock2 windowSize (output ++ block1 ++ block2) prevHuff prevFse history
          hdr3 afterHdr3 block3 afterBlock3
          hoff3 hparse3 hbs3 hws3 htype3 hraw3 hlast3)))

/-! ## decompressBlocksWF two-block composition theorems -/

/-- When `decompressBlocksWF` encounters two consecutive raw blocks (first non-last,
    second last), the output is `output ++ block1 ++ block2` at the position after
    the second block. Composes `decompressBlocksWF_raw_step` and
    `decompressBlocksWF_single_raw`. -/
theorem decompressBlocksWF_two_raw_blocks (data : ByteArray) (off : Nat)
    (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zstd.Native.ZstdHuffmanTable)
    (prevFse : Zstd.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last raw)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterBlock1 : Nat)
    -- Block 2 (last raw)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterBlock2 : Nat)
    -- Block 1 hypotheses
    (hoff1 : ¬ data.size ≤ off)
    (hparse1 : Zstd.Native.parseBlockHeader data off = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize))
    (htype1 : hdr1.blockType = .raw)
    (hraw1 : Zstd.Native.decompressRawBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterBlock1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterBlock1 ≤ off)
    -- Block 2 hypotheses
    (hoff2 : ¬ data.size ≤ afterBlock1)
    (hparse2 : Zstd.Native.parseBlockHeader data afterBlock1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (windowSize > 0 && hdr2.blockSize.toUInt64 > windowSize))
    (htype2 : hdr2.blockType = .raw)
    (hraw2 : Zstd.Native.decompressRawBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterBlock2))
    (hlast2 : hdr2.lastBlock = true) :
    Zstd.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ block1 ++ block2, afterBlock2) := by
  rw [decompressBlocksWF_raw_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 afterBlock1 hoff1 hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1]
  rw [decompressBlocksWF_single_raw data afterBlock1 windowSize (output ++ block1) prevHuff
    prevFse history hdr2 afterHdr2 block2 afterBlock2 hoff2 hparse2 hbs2 hws2 htype2 hraw2
    hlast2]

/-- When `decompressBlocksWF` encounters two consecutive RLE blocks (first non-last,
    second last), the output is `output ++ block1 ++ block2` at the position after
    the second block's byte. Composes `decompressBlocksWF_rle_step` and
    `decompressBlocksWF_single_rle`. -/
theorem decompressBlocksWF_two_rle_blocks (data : ByteArray) (off : Nat)
    (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zstd.Native.ZstdHuffmanTable)
    (prevFse : Zstd.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last RLE)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterByte1 : Nat)
    -- Block 2 (last RLE)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterByte2 : Nat)
    -- Block 1 hypotheses
    (hoff1 : ¬ data.size ≤ off)
    (hparse1 : Zstd.Native.parseBlockHeader data off = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize))
    (htype1 : hdr1.blockType = .rle)
    (hrle1 : Zstd.Native.decompressRLEBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterByte1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterByte1 ≤ off)
    -- Block 2 hypotheses
    (hoff2 : ¬ data.size ≤ afterByte1)
    (hparse2 : Zstd.Native.parseBlockHeader data afterByte1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (windowSize > 0 && hdr2.blockSize.toUInt64 > windowSize))
    (htype2 : hdr2.blockType = .rle)
    (hrle2 : Zstd.Native.decompressRLEBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterByte2))
    (hlast2 : hdr2.lastBlock = true) :
    Zstd.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ block1 ++ block2, afterByte2) := by
  rw [decompressBlocksWF_rle_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 afterByte1 hoff1 hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1]
  rw [decompressBlocksWF_single_rle data afterByte1 windowSize (output ++ block1) prevHuff
    prevFse history hdr2 afterHdr2 block2 afterByte2 hoff2 hparse2 hbs2 hws2 htype2 hrle2
    hlast2]

/-! ## decompressBlocksWF two-block composed completeness (homogeneous) -/

/-- When two consecutive raw blocks are encoded at byte level (first non-last at `off`,
    second last at `off2`), `decompressBlocksWF` succeeds. Composes
    `parseBlockHeader_succeeds` + field characterization + `decompressRawBlock_succeeds`
    for block 1, then `decompressBlocksWF_raw_step` to advance, and
    `decompressBlocksWF_succeeds_single_raw` for block 2. -/
theorem decompressBlocksWF_succeeds_two_raw_blocks (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zstd.Native.ZstdHuffmanTable)
    (prevFse : Zstd.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 byte-level conditions (non-last raw at off)
    (hsize1 : data.size ≥ off + 3)
    (htypeVal1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit1 : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload1 : data.size ≥ off + 3 +
        (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Position: off2 is after block 1 (3-byte header + blockSize payload)
    (hoff2 : off2 = off + 3 +
        (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 byte-level conditions (last raw at off2)
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) :
    ∃ result pos',
      Zstd.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Block 1: parseBlockHeader succeeds (typeVal=0 ≠ 3)
  have htypeNe3_1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal1]; decide
  obtain ⟨hdr1, afterHdr1, hparse1⟩ := parseBlockHeader_succeeds data off hsize1 htypeNe3_1
  -- Block 1: field characterization
  have htype1 := (parseBlockHeader_blockType_eq data off hdr1 afterHdr1 hparse1).1 htypeVal1
  have hbs1_eq := parseBlockHeader_blockSize_eq data off hdr1 afterHdr1 hparse1
  have hpos1_eq := parseBlockHeader_pos_eq data off hdr1 afterHdr1 hparse1
  have hnotlast1 : hdr1.lastBlock = false := by
    rw [parseBlockHeader_lastBlock_eq data off hdr1 afterHdr1 hparse1, hlastBit1]; decide
  have hbs1 : ¬ hdr1.blockSize > 131072 := by rw [hbs1_eq]; exact Nat.not_lt.mpr hblockSize1
  have hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize) := by
    rw [hbs1_eq]; exact hwindow1
  -- Block 1: decompressRawBlock succeeds
  have hpayload1' : data.size ≥ afterHdr1 + hdr1.blockSize.toNat := by
    rw [hpos1_eq, hbs1_eq]; omega
  obtain ⟨block1, afterBlock1, hraw1⟩ := decompressRawBlock_succeeds data afterHdr1
    hdr1.blockSize hpayload1'
  -- Position threading: afterBlock1 = off2
  have hAfterBlock1 : afterBlock1 = off2 := by
    rw [decompressRawBlock_pos_eq data afterHdr1 hdr1.blockSize block1 afterBlock1 hraw1,
      hpos1_eq, hbs1_eq]; exact hoff2.symm
  -- Apply raw step for block 1, rewrite position to off2
  have hoff1 : ¬ data.size ≤ off := by omega
  have hadv1 : ¬ afterBlock1 ≤ off := by rw [hAfterBlock1, hoff2]; omega
  rw [decompressBlocksWF_raw_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 afterBlock1 hoff1 hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1,
    hAfterBlock1]
  -- Apply single raw succeeds for block 2
  exact decompressBlocksWF_succeeds_single_raw data off2 windowSize (output ++ block1)
    prevHuff prevFse history hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2

/-- When two consecutive RLE blocks are encoded at byte level (first non-last at `off`,
    second last at `off2`), `decompressBlocksWF` succeeds. Composes
    `parseBlockHeader_succeeds` + field characterization + `decompressRLEBlock_succeeds`
    for block 1, then `decompressBlocksWF_rle_step` to advance, and
    `decompressBlocksWF_succeeds_single_rle` for block 2. -/
theorem decompressBlocksWF_succeeds_two_rle_blocks (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zstd.Native.ZstdHuffmanTable)
    (prevFse : Zstd.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 byte-level conditions (non-last RLE at off)
    (hsize1 : data.size ≥ off + 3)
    (htypeVal1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit1 : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload1 : data.size ≥ off + 4)
    -- Position: off2 is after block 1 (3-byte header + 1-byte RLE payload)
    (hoff2 : off2 = off + 4)
    -- Block 2 byte-level conditions (last RLE at off2)
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload2 : data.size ≥ off2 + 4) :
    ∃ result pos',
      Zstd.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Block 1: parseBlockHeader succeeds (typeVal=1 ≠ 3)
  have htypeNe3_1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal1]; decide
  obtain ⟨hdr1, afterHdr1, hparse1⟩ := parseBlockHeader_succeeds data off hsize1 htypeNe3_1
  -- Block 1: field characterization
  have htype1 := (parseBlockHeader_blockType_eq data off hdr1 afterHdr1 hparse1).2.1 htypeVal1
  have hbs1_eq := parseBlockHeader_blockSize_eq data off hdr1 afterHdr1 hparse1
  have hpos1_eq := parseBlockHeader_pos_eq data off hdr1 afterHdr1 hparse1
  have hnotlast1 : hdr1.lastBlock = false := by
    rw [parseBlockHeader_lastBlock_eq data off hdr1 afterHdr1 hparse1, hlastBit1]; decide
  have hbs1 : ¬ hdr1.blockSize > 131072 := by rw [hbs1_eq]; exact Nat.not_lt.mpr hblockSize1
  have hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize) := by
    rw [hbs1_eq]; exact hwindow1
  -- Block 1: decompressRLEBlock succeeds (afterHdr = off + 3, need 1 byte)
  have hpayload1' : data.size ≥ afterHdr1 + 1 := by rw [hpos1_eq]; omega
  obtain ⟨block1, afterByte1, hrle1⟩ := decompressRLEBlock_succeeds data afterHdr1
    hdr1.blockSize hpayload1'
  -- Position threading: afterByte1 = off2
  have hAfterByte1 : afterByte1 = off2 := by
    rw [decompressRLEBlock_pos_eq data afterHdr1 hdr1.blockSize block1 afterByte1 hrle1,
      hpos1_eq]; omega
  -- Apply RLE step for block 1, rewrite position to off2
  have hoff1 : ¬ data.size ≤ off := by omega
  have hadv1 : ¬ afterByte1 ≤ off := by rw [hAfterByte1, hoff2]; omega
  rw [decompressBlocksWF_rle_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 afterByte1 hoff1 hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1,
    hAfterByte1]
  -- Apply single RLE succeeds for block 2
  exact decompressBlocksWF_succeeds_single_rle data off2 windowSize (output ++ block1)
    prevHuff prevFse history hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2

/-! ## Frame-level wrapping helper -/

/-- When block-level decompression succeeds and the frame has no dictionary,
    no content checksum, and no declared content size, `decompressFrame` succeeds.
    This factors out the common frame-wrapping pattern shared by all frame-level
    completeness theorems. -/
theorem decompressFrame_of_blocks_succeed (data : ByteArray) (pos : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hparse : Zstd.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hnodict : header.dictionaryId = none)
    (hnocksum : header.contentChecksum = false)
    (hnosize : header.contentSize = none)
    (hblocks : ∃ result pos',
      Zstd.Native.decompressBlocksWF data afterHeader header.windowSize
        ByteArray.empty none {} #[1, 4, 8] = .ok (result, pos')) :
    ∃ content pos',
      Zstd.Native.decompressFrame data pos = .ok (content, pos') := by
  obtain ⟨result, blockPos, hblocks⟩ := hblocks
  unfold Zstd.Native.decompressFrame
  simp only [bind, Except.bind, pure, Except.pure, hparse]
  simp only [hnodict]
  unfold Zstd.Native.decompressBlocks
  rw [hblocks]
  simp only [hnocksum, hnosize, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, rfl⟩
/-- When `decompressBlocksWF` encounters a non-last raw block followed by a last
    RLE block, the output is `output ++ block1 ++ block2` at the position after
    the RLE byte. Composes `decompressBlocksWF_raw_step` and
    `decompressBlocksWF_single_rle`. -/
theorem decompressBlocksWF_raw_then_rle (data : ByteArray) (off : Nat)
    (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zstd.Native.ZstdHuffmanTable)
    (prevFse : Zstd.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last raw)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterBlock1 : Nat)
    -- Block 2 (last RLE)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterByte2 : Nat)
    -- Block 1 hypotheses
    (hoff1 : ¬ data.size ≤ off)
    (hparse1 : Zstd.Native.parseBlockHeader data off = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize))
    (htype1 : hdr1.blockType = .raw)
    (hraw1 : Zstd.Native.decompressRawBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterBlock1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterBlock1 ≤ off)
    -- Block 2 hypotheses
    (hoff2 : ¬ data.size ≤ afterBlock1)
    (hparse2 : Zstd.Native.parseBlockHeader data afterBlock1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (windowSize > 0 && hdr2.blockSize.toUInt64 > windowSize))
    (htype2 : hdr2.blockType = .rle)
    (hrle2 : Zstd.Native.decompressRLEBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterByte2))
    (hlast2 : hdr2.lastBlock = true) :
    Zstd.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ block1 ++ block2, afterByte2) := by
  rw [decompressBlocksWF_raw_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 afterBlock1 hoff1 hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1]
  rw [decompressBlocksWF_single_rle data afterBlock1 windowSize (output ++ block1) prevHuff
    prevFse history hdr2 afterHdr2 block2 afterByte2 hoff2 hparse2 hbs2 hws2 htype2 hrle2
    hlast2]

/-- When `decompressBlocksWF` encounters a non-last RLE block followed by a last
    raw block, the output is `output ++ block1 ++ block2` at the position after
    the second block. Composes `decompressBlocksWF_rle_step` and
    `decompressBlocksWF_single_raw`. -/
theorem decompressBlocksWF_rle_then_raw (data : ByteArray) (off : Nat)
    (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zstd.Native.ZstdHuffmanTable)
    (prevFse : Zstd.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last RLE)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterByte1 : Nat)
    -- Block 2 (last raw)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterBlock2 : Nat)
    -- Block 1 hypotheses
    (hoff1 : ¬ data.size ≤ off)
    (hparse1 : Zstd.Native.parseBlockHeader data off = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize))
    (htype1 : hdr1.blockType = .rle)
    (hrle1 : Zstd.Native.decompressRLEBlock data afterHdr1 hdr1.blockSize
               = .ok (block1, afterByte1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterByte1 ≤ off)
    -- Block 2 hypotheses
    (hoff2 : ¬ data.size ≤ afterByte1)
    (hparse2 : Zstd.Native.parseBlockHeader data afterByte1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (windowSize > 0 && hdr2.blockSize.toUInt64 > windowSize))
    (htype2 : hdr2.blockType = .raw)
    (hraw2 : Zstd.Native.decompressRawBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterBlock2))
    (hlast2 : hdr2.lastBlock = true) :
    Zstd.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ block1 ++ block2, afterBlock2) := by
  rw [decompressBlocksWF_rle_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 afterByte1 hoff1 hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1]
  rw [decompressBlocksWF_single_raw data afterByte1 windowSize (output ++ block1) prevHuff
    prevFse history hdr2 afterHdr2 block2 afterBlock2 hoff2 hparse2 hbs2 hws2 htype2 hraw2
    hlast2]

/-! ## decompressBlocksWF two-block composed completeness (heterogeneous raw/RLE) -/

/-- When a non-last raw block at `off` is followed by a last RLE block at `off2`,
    `decompressBlocksWF` succeeds. Composes `decompressBlocksWF_raw_step` with
    `decompressBlocksWF_succeeds_single_rle` using only byte-level preconditions. -/
theorem decompressBlocksWF_succeeds_raw_then_rle (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zstd.Native.ZstdHuffmanTable)
    (prevFse : Zstd.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last raw) byte-level conditions at off
    (hsize1 : data.size ≥ off + 3)
    (htypeVal1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit1 : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload1 : data.size ≥ off + 3 +
        (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- off2 = position after block 1's raw payload
    (hoff2 : off2 = off + 3 + (((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last RLE) byte-level conditions at off2
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload2 : data.size ≥ off2 + 4) :
    ∃ result pos',
      Zstd.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Block 1: parseBlockHeader succeeds (typeVal=0 ≠ 3)
  have htypeNe3 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal1]; decide
  obtain ⟨hdr1, afterHdr1, hparse1⟩ := parseBlockHeader_succeeds data off hsize1 htypeNe3
  have htype1 := (parseBlockHeader_blockType_eq data off hdr1 afterHdr1 hparse1).1 htypeVal1
  have hbs_eq1 := parseBlockHeader_blockSize_eq data off hdr1 afterHdr1 hparse1
  have hpos_eq1 := parseBlockHeader_pos_eq data off hdr1 afterHdr1 hparse1
  have hnotlast1 : hdr1.lastBlock = false := by
    rw [parseBlockHeader_lastBlock_eq data off hdr1 afterHdr1 hparse1, hlastBit1]; decide
  have hbs1 : ¬ hdr1.blockSize > 131072 := by rw [hbs_eq1]; exact Nat.not_lt.mpr hblockSize1
  have hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize) := by
    rw [hbs_eq1]; exact hwindow1
  -- Block 1: decompressRawBlock succeeds
  have hpayload1' : data.size ≥ afterHdr1 + hdr1.blockSize.toNat := by
    rw [hpos_eq1, hbs_eq1]; omega
  obtain ⟨block1, afterBlock1, hraw1⟩ := decompressRawBlock_succeeds data afterHdr1
    hdr1.blockSize hpayload1'
  have hoff1 : ¬ data.size ≤ off := by omega
  have hRawPos := decompressRawBlock_pos_eq data afterHdr1 hdr1.blockSize block1
    afterBlock1 hraw1
  have hadv1 : ¬ afterBlock1 ≤ off := by rw [hRawPos, hpos_eq1]; omega
  -- afterBlock1 = off2, substitute
  have : off2 = afterBlock1 := by rw [hoff2, hRawPos, hpos_eq1, hbs_eq1]
  subst this
  -- Step through block 1, then apply succeeds_single_rle for block 2
  rw [decompressBlocksWF_raw_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 off2 hoff1 hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1]
  exact decompressBlocksWF_succeeds_single_rle data off2 windowSize (output ++ block1)
    prevHuff prevFse history hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2

/-- When a non-last RLE block at `off` is followed by a last raw block at `off2`,
    `decompressBlocksWF` succeeds. Composes `decompressBlocksWF_rle_step` with
    `decompressBlocksWF_succeeds_single_raw` using only byte-level preconditions. -/
theorem decompressBlocksWF_succeeds_rle_then_raw (data : ByteArray)
    (off off2 : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zstd.Native.ZstdHuffmanTable)
    (prevFse : Zstd.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last RLE) byte-level conditions at off
    (hsize1 : data.size ≥ off + 3)
    (htypeVal1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 1)
    (hlastBit1 : (data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) &&& 1 = 0)
    (hblockSize1 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
        ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow1 : ¬ (windowSize > 0 &&
        ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
          ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload1 : data.size ≥ off + 4)
    -- off2 = position after block 1's RLE byte
    (hoff2 : off2 = off + 4)
    -- Block 2 (last raw) byte-level conditions at off2
    (hsize2 : data.size ≥ off2 + 3)
    (htypeVal2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 0)
    (hlastBit2 : (data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) &&& 1 = 1)
    (hblockSize2 : ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
        ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3) ≤ 131072)
    (hwindow2 : ¬ (windowSize > 0 &&
        ((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toUInt64 > windowSize))
    (hpayload2 : data.size ≥ off2 + 3 +
        (((data[off2]!.toUInt32 ||| (data[off2 + 1]!.toUInt32 <<< 8)
          ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) :
    ∃ result pos',
      Zstd.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
        = .ok (result, pos') := by
  -- Block 1: parseBlockHeader succeeds (typeVal=1 ≠ 3)
  have htypeNe3 : ((data[off]!.toUInt32 ||| (data[off + 1]!.toUInt32 <<< 8)
      ||| (data[off + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 ≠ 3 := by
    rw [htypeVal1]; decide
  obtain ⟨hdr1, afterHdr1, hparse1⟩ := parseBlockHeader_succeeds data off hsize1 htypeNe3
  have htype1 := (parseBlockHeader_blockType_eq data off hdr1 afterHdr1 hparse1).2.1 htypeVal1
  have hbs_eq1 := parseBlockHeader_blockSize_eq data off hdr1 afterHdr1 hparse1
  have hpos_eq1 := parseBlockHeader_pos_eq data off hdr1 afterHdr1 hparse1
  have hnotlast1 : hdr1.lastBlock = false := by
    rw [parseBlockHeader_lastBlock_eq data off hdr1 afterHdr1 hparse1, hlastBit1]; decide
  have hbs1 : ¬ hdr1.blockSize > 131072 := by rw [hbs_eq1]; exact Nat.not_lt.mpr hblockSize1
  have hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize) := by
    rw [hbs_eq1]; exact hwindow1
  -- Block 1: decompressRLEBlock succeeds
  have hpayload1' : data.size ≥ afterHdr1 + 1 := by rw [hpos_eq1]; omega
  obtain ⟨block1, afterByte1, hrle1⟩ := decompressRLEBlock_succeeds data afterHdr1
    hdr1.blockSize hpayload1'
  have hoff1 : ¬ data.size ≤ off := by omega
  have hRlePos := decompressRLEBlock_pos_eq data afterHdr1 hdr1.blockSize block1
    afterByte1 hrle1
  have hadv1 : ¬ afterByte1 ≤ off := by rw [hRlePos, hpos_eq1]; omega
  -- afterByte1 = off2, substitute
  have : off2 = afterByte1 := by rw [hoff2, hRlePos, hpos_eq1]
  subst this
  -- Step through block 1, then apply succeeds_single_raw for block 2
  rw [decompressBlocksWF_rle_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 off2 hoff1 hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1]
  exact decompressBlocksWF_succeeds_single_raw data off2 windowSize (output ++ block1)
    prevHuff prevFse history hsize2 htypeVal2 hlastBit2 hblockSize2 hwindow2 hpayload2
/-! ## Frame header position advancement -/

set_option maxHeartbeats 400000 in
/-- When `parseFrameHeader` succeeds, the returned position advances by at
    least 5 (4 magic bytes + 1 descriptor byte). In practice the minimum
    is 6 bytes (singleSegment frames have at least 1 byte of content size). -/
theorem parseFrameHeader_pos_ge_five (data : ByteArray) (pos : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (pos' : Nat)
    (h : Zstd.Native.parseFrameHeader data pos = .ok (header, pos')) :
    pos' ≥ pos + 5 := by
  unfold Zstd.Native.parseFrameHeader at h
  dsimp only [Bind.bind, Except.bind] at h
  by_cases h1 : data.size < pos + 4
  · rw [if_pos h1] at h; exact nomatch h
  · rw [if_neg h1] at h
    simp only [pure, Pure.pure] at h
    by_cases h2 : (Binary.readUInt32LE data pos != Zstd.Native.zstdMagic) = true
    · rw [if_pos h2] at h; exact nomatch h
    · rw [if_neg h2] at h
      by_cases h3 : data.size < pos + 4 + 1
      · rw [if_pos h3] at h; exact nomatch h
      · rw [if_neg h3] at h
        split at h
        · exact nomatch h
        · simp only [Except.pure] at h
          repeat split at h
          iterate 5 (all_goals (try (first | contradiction | (split at h))))
          all_goals first
            | contradiction
            | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
               obtain ⟨-, rfl⟩ := h; omega)

set_option maxHeartbeats 400000 in
/-- When `parseFrameHeader` succeeds, the returned position is strictly greater
    than the input position. The header is at least 6 bytes (4 magic + 1
    descriptor + at least 1 byte for window descriptor or content size). -/
theorem parseFrameHeader_pos_gt (data : ByteArray) (pos : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (pos' : Nat)
    (h : Zstd.Native.parseFrameHeader data pos = .ok (header, pos')) :
    pos' > pos := by
  have := parseFrameHeader_pos_ge_five data pos header pos' h; omega

set_option maxHeartbeats 400000 in
/-- When `parseFrameHeader` succeeds, the returned position is within data bounds.
    Each stage of the header has a bounds check (`data.size < off + N → throw`),
    so on the success path, `off + N ≤ data.size` holds at every stage. The final
    returned position is the last `off`, bounded by the last check. -/
theorem parseFrameHeader_le_size (data : ByteArray) (pos : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (pos' : Nat)
    (h : Zstd.Native.parseFrameHeader data pos = .ok (header, pos')) :
    pos' ≤ data.size := by
  unfold Zstd.Native.parseFrameHeader at h
  dsimp only [Bind.bind, Except.bind] at h
  by_cases h1 : data.size < pos + 4
  · rw [if_pos h1] at h; exact nomatch h
  · rw [if_neg h1] at h
    simp only [pure, Pure.pure] at h
    by_cases h2 : (Binary.readUInt32LE data pos != Zstd.Native.zstdMagic) = true
    · rw [if_pos h2] at h; exact nomatch h
    · rw [if_neg h2] at h
      by_cases h3 : data.size < pos + 4 + 1
      · rw [if_pos h3] at h; exact nomatch h
      · rw [if_neg h3] at h
        split at h
        · exact nomatch h
        · simp only [Except.pure] at h
          repeat split at h
          iterate 5 (all_goals (try (first | contradiction | (split at h))))
          all_goals first
            | contradiction
            | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
               obtain ⟨-, rfl⟩ := h; omega)

/-! ## Parsing completeness -/

/-- Minimum data size required for `parseFrameHeader` to succeed, given
    the frame header descriptor byte. The descriptor byte (at `pos + 4`)
    determines the sizes of optional header fields:
    - Window descriptor: 0 or 1 byte (absent if `singleSegment` flag set)
    - Dictionary ID: 0, 1, 2, or 4 bytes (from `didFlag` bits 1-0)
    - Frame content size: 0, 1, 2, 4, or 8 bytes (from `fcsFlag` bits 7-6) -/
def frameHeaderMinSize (desc : UInt8) : Nat :=
  let fcsFlag := (desc >>> 6).toNat
  let singleSegment := (desc >>> 5) &&& 1 == 1
  let didFlag := (desc &&& 3).toNat
  let windowDescSize := if singleSegment then 0 else 1
  let didSize := match didFlag with | 1 => 1 | 2 => 2 | 3 => 4 | _ => 0
  let fcsSize := match fcsFlag with
    | 0 => if singleSegment then 1 else 0
    | 1 => 2 | 2 => 4 | _ => 8
  4 + 1 + windowDescSize + didSize + fcsSize

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
set_option linter.unusedSimpArgs false in
/-- When the data has the correct Zstd magic number and enough bytes for the
    full header (as determined by the descriptor byte at `pos + 4`),
    `parseFrameHeader` succeeds. -/
theorem parseFrameHeader_succeeds (data : ByteArray) (pos : Nat)
    (hmagic : Binary.readUInt32LE data pos = Zstd.Native.zstdMagic)
    (hsize : data.size ≥ pos + frameHeaderMinSize data[pos + 4]!) :
    ∃ hdr afterHdr, Zstd.Native.parseFrameHeader data pos = .ok (hdr, afterHdr) := by
  have hmin : frameHeaderMinSize data[pos + 4]! ≥ 6 := by
    have h : ∀ i : Fin 256, frameHeaderMinSize ⟨⟨i⟩⟩ ≥ 6 := by decide
    exact h data[pos + 4]!.toBitVec.toFin
  -- Backward approach: case-split on the result
  cases hres : Zstd.Native.parseFrameHeader data pos with
  | ok val => obtain ⟨hdr, pos'⟩ := val; exact ⟨hdr, pos', rfl⟩
  | error e =>
    exfalso
    -- Single-pass simp to reduce all monadic constructs
    simp only [Zstd.Native.parseFrameHeader, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at hres
    unfold frameHeaderMinSize at hsize
    dsimp only [] at hsize
    -- Guard 1: magic size
    rw [if_neg (show ¬(data.size < pos + 4) from by omega)] at hres
    -- Guard 2: magic value
    rw [hmagic] at hres
    simp only [Zstd.Native.zstdMagic, bne_self_eq_false, Bool.false_eq_true, ite_false] at hres
    -- Guard 3: descriptor size
    rw [if_neg (show ¬(data.size < pos + 4 + 1) from by omega)] at hres
    -- Reduce `Zstd.Native.readByte` to `data[...]!` so generalizes align with hsize.
    simp only [readByte_eq_getElem] at hres
    -- Remaining guards depend on descriptor byte fields. Generalize them
    -- so case analysis gives consistent values in hsize.
    generalize hss : (data[pos + 4]! >>> 5 &&& 1 == 1) = ss at hres hsize
    generalize hdf : (data[pos + 4]! &&& 3).toNat = df at hres hsize
    generalize hff : (data[pos + 4]! >>> 6).toNat = ff at hres hsize
    -- Case-split on singleSegment; simp resolves both hres and hsize
    by_cases hss_val : ss = true
    · -- singleSegment = true: no window descriptor
      simp only [hss_val, Bool.not_true, Bool.false_eq_true, ite_false, ite_true] at hres hsize
      -- Walk through didFlag + fcsSize guards via split.
      -- contradiction closes ok branches (.ok _ = .error _)
      -- omega closes error branches (guard contradicts hsize)
      repeat (first | contradiction | (simp only [Bool.false_eq_true, ite_false, ite_true] at hsize; omega) | (split at hres))
    · -- singleSegment = false: window descriptor present
      have hss_false : ss = false := by cases ss <;> first | rfl | exact absurd rfl hss_val
      simp only [hss_false, Bool.not_false, ite_true, ite_false,
        Bool.false_eq_true] at hres hsize
      -- Window descriptor guard
      rw [if_neg (show ¬(data.size < pos + 4 + 1 + 1) from by omega)] at hres
      -- Walk through remaining guards
      repeat (first | contradiction | (simp only [Bool.false_eq_true, ite_false, ite_true] at hsize; omega) | (split at hres))

/-! ## parseFrameHeader field characterization -/

set_option maxHeartbeats 400000 in
/-- When `parseFrameHeader` succeeds, the `contentChecksum` field equals
    bit 2 of the descriptor byte at `pos + 4`. -/
theorem parseFrameHeader_contentChecksum_eq (data : ByteArray) (pos : Nat)
    (hdr : Zstd.Native.ZstdFrameHeader) (pos' : Nat)
    (h : Zstd.Native.parseFrameHeader data pos = .ok (hdr, pos')) :
    hdr.contentChecksum = ((data[pos + 4]! >>> 2) &&& 1 == 1) := by
  unfold Zstd.Native.parseFrameHeader at h
  dsimp only [Bind.bind, Except.bind] at h
  by_cases h1 : data.size < pos + 4
  · rw [if_pos h1] at h; exact nomatch h
  · rw [if_neg h1] at h
    simp only [pure, Pure.pure] at h
    by_cases h2 : (Binary.readUInt32LE data pos != Zstd.Native.zstdMagic) = true
    · rw [if_pos h2] at h; exact nomatch h
    · rw [if_neg h2] at h
      by_cases h3 : data.size < pos + 4 + 1
      · rw [if_pos h3] at h; exact nomatch h
      · rw [if_neg h3] at h
        split at h
        · exact nomatch h
        · simp only [Except.pure] at h
          repeat split at h
          iterate 5 (all_goals (try (first | contradiction | (split at h))))
          all_goals first
            | contradiction
            | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
               obtain ⟨rfl, rfl⟩ := h; simp)

set_option maxHeartbeats 400000 in
/-- When `parseFrameHeader` succeeds, the `singleSegment` field equals
    bit 5 of the descriptor byte at `pos + 4`. -/
theorem parseFrameHeader_singleSegment_eq (data : ByteArray) (pos : Nat)
    (hdr : Zstd.Native.ZstdFrameHeader) (pos' : Nat)
    (h : Zstd.Native.parseFrameHeader data pos = .ok (hdr, pos')) :
    hdr.singleSegment = ((data[pos + 4]! >>> 5) &&& 1 == 1) := by
  unfold Zstd.Native.parseFrameHeader at h
  dsimp only [Bind.bind, Except.bind] at h
  by_cases h1 : data.size < pos + 4
  · rw [if_pos h1] at h; exact nomatch h
  · rw [if_neg h1] at h
    simp only [pure, Pure.pure] at h
    by_cases h2 : (Binary.readUInt32LE data pos != Zstd.Native.zstdMagic) = true
    · rw [if_pos h2] at h; exact nomatch h
    · rw [if_neg h2] at h
      by_cases h3 : data.size < pos + 4 + 1
      · rw [if_pos h3] at h; exact nomatch h
      · rw [if_neg h3] at h
        split at h
        · exact nomatch h
        · simp only [Except.pure] at h
          repeat split at h
          iterate 5 (all_goals (try (first | contradiction | (split at h))))
          all_goals first
            | contradiction
            | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
               obtain ⟨rfl, rfl⟩ := h; simp)

set_option maxHeartbeats 800000 in
/-- When `parseFrameHeader` succeeds, the `dictionaryId` field is determined
    by bits 0-1 of the descriptor byte (DID_Field_Size) and the subsequent
    0/1/2/4 bytes. The DID offset depends on the singleSegment flag:
    `pos + 5` if singleSegment (no window descriptor), `pos + 6` otherwise. -/
theorem parseFrameHeader_dictionaryId_eq (data : ByteArray) (pos : Nat)
    (hdr : Zstd.Native.ZstdFrameHeader) (pos' : Nat)
    (h : Zstd.Native.parseFrameHeader data pos = .ok (hdr, pos')) :
    let desc := data[pos + 4]!
    let didFlag := (desc &&& 3).toNat
    let didOff := if (desc >>> 5) &&& 1 == 1 then pos + 5 else pos + 6
    (didFlag = 0 → hdr.dictionaryId = none) ∧
    (didFlag = 1 → hdr.dictionaryId = some data[didOff]!.toUInt32) ∧
    (didFlag = 2 → hdr.dictionaryId = some (Binary.readUInt16LE data didOff).toUInt32) ∧
    (didFlag = 3 → hdr.dictionaryId = some (Binary.readUInt32LE data didOff)) := by
  unfold Zstd.Native.parseFrameHeader at h
  dsimp only [Bind.bind, Except.bind] at h
  by_cases h1 : data.size < pos + 4
  · rw [if_pos h1] at h; exact nomatch h
  · rw [if_neg h1] at h
    simp only [pure, Pure.pure] at h
    by_cases h2 : (Binary.readUInt32LE data pos != Zstd.Native.zstdMagic) = true
    · rw [if_pos h2] at h; exact nomatch h
    · rw [if_neg h2] at h
      by_cases h3 : data.size < pos + 4 + 1
      · rw [if_pos h3] at h; exact nomatch h
      · rw [if_neg h3] at h
        split at h
        · exact nomatch h
        · simp only [Except.pure] at h
          repeat split at h
          iterate 5 (all_goals (try (first | contradiction | (split at h))))
          all_goals first
            | contradiction
            | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
               obtain ⟨rfl, rfl⟩ := h
               simp only [readByte_eq_getElem] at *
               grind)

/-! ## Window size characterizing properties -/

set_option maxRecDepth 1024 in
/-- The minimum window size is 1KB (RFC 8878 §3.1.1.1.2: windowLog ≥ 10,
    so windowBase ≥ 2^10 = 1024 and windowAdd ≥ 0). -/
theorem windowSizeFromDescriptor_ge_1024 (d : UInt8) :
    Zstd.Native.windowSizeFromDescriptor d ≥ 1024 := by
  have h : ∀ i : Fin 256, Zstd.Native.windowSizeFromDescriptor ⟨⟨i⟩⟩ ≥ 1024 := by decide
  exact h d.toBitVec.toFin

/-- The window size is always positive (follows from `windowSizeFromDescriptor_ge_1024`). -/
theorem windowSizeFromDescriptor_pos (d : UInt8) :
    Zstd.Native.windowSizeFromDescriptor d > 0 := by
  exact Nat.lt_of_lt_of_le (by decide : (0 : UInt64) < 1024) (windowSizeFromDescriptor_ge_1024 d)


end Zstd.Spec
