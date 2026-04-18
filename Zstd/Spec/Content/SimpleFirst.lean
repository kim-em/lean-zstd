import Zstd.Spec.Succeeds

/-!
# Zstandard Frame Specification — Simple-First Two-Block Content

Frame-level content characterization theorems for two-block frames where
the first block is raw or RLE followed by a last compressed block
(literals-only or sequences). Also includes `decompressBlocksWF` helper
lemmas that compose raw/RLE steps with single compressed-sequences blocks.
-/

-- Unfold `decompressFrame`, substitute `hh` (parseFrameHeader result) and `hblocks`
-- (block-loop result), then handle the dictionary check and close both branches with grind.
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

/-- When `decompressFrame` succeeds and the frame contains a non-last raw block
    followed by a last compressed block with numSeq=0 (literals only), the output
    equals `block1 ++ literals2`. Raw blocks don't modify Huffman/FSE state, so
    block 2's `parseLiteralsSection` receives `none` for prevHuff. -/
theorem decompressFrame_raw_then_compressed_lit_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last raw)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterBlock1 : Nat)
    -- Block 2 (last compressed, numSeq=0)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zstd.Native.ZstdHuffmanTable)
    (modes2 : Zstd.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
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
    -- Block 2 hypotheses (compressed, last, numSeq=0)
    (hoff2 : ¬ data.size ≤ afterBlock1)
    (hparse2 : Zstd.Native.parseBlockHeader data afterBlock1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zstd.Native.parseLiteralsSection data afterHdr2 none
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zstd.Native.parseSequencesHeader data afterLiterals2
               = .ok (0, modes2, afterSeqHeader2))
    (hlast2 : hdr2.lastBlock = true) :
    output = block1 ++ literals2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_raw_then_compressed_literals data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
    block1 afterBlock1 hdr2 afterHdr2 literals2 afterLiterals2
    huffTree2 modes2 afterSeqHeader2
    hoff hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a non-last RLE block
    followed by a last compressed block with numSeq=0 (literals only), the output
    equals `block1 ++ literals2`. RLE blocks don't modify Huffman/FSE state, so
    block 2's `parseLiteralsSection` receives `none` for prevHuff. -/
theorem decompressFrame_rle_then_compressed_lit_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last RLE)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (block1 : ByteArray) (afterByte1 : Nat)
    -- Block 2 (last compressed, numSeq=0)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zstd.Native.ZstdHuffmanTable)
    (modes2 : Zstd.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
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
    -- Block 2 hypotheses (compressed, last, numSeq=0)
    (hoff2 : ¬ data.size ≤ afterByte1)
    (hparse2 : Zstd.Native.parseBlockHeader data afterByte1 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zstd.Native.parseLiteralsSection data afterHdr2 none
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zstd.Native.parseSequencesHeader data afterLiterals2
               = .ok (0, modes2, afterSeqHeader2))
    (hlast2 : hdr2.lastBlock = true) :
    output = block1 ++ literals2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_rle_then_compressed_literals data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
    block1 afterByte1 hdr2 afterHdr2 literals2 afterLiterals2
    huffTree2 modes2 afterSeqHeader2
    hoff hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hlast2
  frame_from_blocks

/-- When `decompressBlocksWF` encounters a non-last raw block followed by a
    last compressed block with sequences (numSeq > 0), the output is
    `output ++ block1 ++ blockOutput2` at the position after the compressed block.
    Raw blocks don't modify Huffman/FSE state or offset history, so block 2
    receives the original `prevHuff`, `prevFse`, and `history`.

    Composes `decompressBlocksWF_raw_step` and
    `decompressBlocksWF_single_compressed_sequences`. -/
theorem decompressBlocksWF_raw_then_compressed_sequences (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zstd.Native.ZstdHuffmanTable)
    (prevFse : Zstd.Native.PrevFseTables) (history : Array Nat)
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
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zstd.Native.parseLiteralsSection data afterHdr2 prevHuff
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zstd.Native.parseSequencesHeader data afterLiterals2
               = .ok (numSeq2, modes2, afterSeqHeader2))
    (hNumSeq2 : ¬ numSeq2 == 0)
    (hfse2 : Zstd.Native.resolveSequenceFseTables modes2 data afterSeqHeader2 prevFse
               = .ok (llTable2, ofTable2, mlTable2, afterTables2))
    (hbbr2 : Zstd.Native.BackwardBitReader.init data afterTables2
               (afterHdr2 + hdr2.blockSize.toNat) = .ok bbr2)
    (hdec2 : Zstd.Native.decodeSequences llTable2 ofTable2 mlTable2 bbr2 numSeq2
               = .ok sequences2)
    (hexec2 : Zstd.Native.executeSequences sequences2 literals2
                (if windowSize > 0 && (output ++ block1).size > windowSize.toNat
                 then (output ++ block1).extract
                   ((output ++ block1).size - windowSize.toNat)
                   (output ++ block1).size
                 else output ++ block1)
                history windowSize.toNat
                = .ok (blockOutput2, newHist2))
    (hlast2 : hdr2.lastBlock = true) :
    Zstd.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ block1 ++ blockOutput2,
             afterHdr2 + hdr2.blockSize.toNat) := by
  rw [decompressBlocksWF_raw_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 afterBlock1 hoff1 hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1]
  exact decompressBlocksWF_single_compressed_sequences data
    afterBlock1 windowSize (output ++ block1) prevHuff prevFse history
    hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
    llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hNumSeq2 hfse2 hbbr2
    hdec2 hexec2 hlast2

/-- When `decompressBlocksWF` encounters a non-last RLE block followed by a
    last compressed block with sequences (numSeq > 0), the output is
    `output ++ block1 ++ blockOutput2` at the position after the compressed block.
    RLE blocks don't modify Huffman/FSE state or offset history, so block 2
    receives the original `prevHuff`, `prevFse`, and `history`.

    Composes `decompressBlocksWF_rle_step` and
    `decompressBlocksWF_single_compressed_sequences`. -/
theorem decompressBlocksWF_rle_then_compressed_sequences (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zstd.Native.ZstdHuffmanTable)
    (prevFse : Zstd.Native.PrevFseTables) (history : Array Nat)
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
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zstd.Native.parseLiteralsSection data afterHdr2 prevHuff
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zstd.Native.parseSequencesHeader data afterLiterals2
               = .ok (numSeq2, modes2, afterSeqHeader2))
    (hNumSeq2 : ¬ numSeq2 == 0)
    (hfse2 : Zstd.Native.resolveSequenceFseTables modes2 data afterSeqHeader2 prevFse
               = .ok (llTable2, ofTable2, mlTable2, afterTables2))
    (hbbr2 : Zstd.Native.BackwardBitReader.init data afterTables2
               (afterHdr2 + hdr2.blockSize.toNat) = .ok bbr2)
    (hdec2 : Zstd.Native.decodeSequences llTable2 ofTable2 mlTable2 bbr2 numSeq2
               = .ok sequences2)
    (hexec2 : Zstd.Native.executeSequences sequences2 literals2
                (if windowSize > 0 && (output ++ block1).size > windowSize.toNat
                 then (output ++ block1).extract
                   ((output ++ block1).size - windowSize.toNat)
                   (output ++ block1).size
                 else output ++ block1)
                history windowSize.toNat
                = .ok (blockOutput2, newHist2))
    (hlast2 : hdr2.lastBlock = true) :
    Zstd.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ block1 ++ blockOutput2,
             afterHdr2 + hdr2.blockSize.toNat) := by
  rw [decompressBlocksWF_rle_step data off windowSize output prevHuff prevFse history
    hdr1 afterHdr1 block1 afterByte1 hoff1 hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1]
  exact decompressBlocksWF_single_compressed_sequences data
    afterByte1 windowSize (output ++ block1) prevHuff prevFse history
    hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
    llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hNumSeq2 hfse2 hbbr2
    hdec2 hexec2 hlast2
/-- When `decompressFrame` succeeds and the frame contains a non-last raw block
    followed by a last compressed block with numSeq>0 (sequences), the output
    equals `block1 ++ blockOutput2`. The raw block contributes `block1` directly;
    the compressed-sequences block produces `blockOutput2` via sequence execution.
    Raw blocks don't modify Huffman/FSE state, so block 2 receives the initial
    `none`/`{}` state. -/
theorem decompressFrame_raw_then_compressed_seq_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
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
    (hlast2 : hdr2.lastBlock = true) :
    output = block1 ++ blockOutput2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Bridge executeSequences: frame starts with empty output, so window uses block1 directly
  have hexec2' : Zstd.Native.executeSequences sequences2 literals2
      (if header.windowSize > 0 && (ByteArray.empty ++ block1).size > header.windowSize.toNat
       then (ByteArray.empty ++ block1).extract
         ((ByteArray.empty ++ block1).size - header.windowSize.toNat)
         (ByteArray.empty ++ block1).size
       else ByteArray.empty ++ block1)
      #[1, 4, 8] header.windowSize.toNat
      = .ok (blockOutput2, newHist2) := by
    simp only [ByteArray.empty_append]
    exact hexec2
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_raw_then_compressed_sequences data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
    block1 afterBlock1
    hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
    llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2
    hoff hparse1 hbs1 hws1 htype1 hraw1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hNumSeq2 hfse2 hbbr2
    hdec2 hexec2' hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a non-last RLE block
    followed by a last compressed block with numSeq>0 (sequences), the output
    equals `block1 ++ blockOutput2`. The RLE block contributes `block1` directly;
    the compressed-sequences block produces `blockOutput2` via sequence execution.
    RLE blocks don't modify Huffman/FSE state, so block 2 receives the initial
    `none`/`{}` state. -/
theorem decompressFrame_rle_then_compressed_seq_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
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
    (hlast2 : hdr2.lastBlock = true) :
    output = block1 ++ blockOutput2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Bridge executeSequences: frame starts with empty output, so window uses block1 directly
  have hexec2' : Zstd.Native.executeSequences sequences2 literals2
      (if header.windowSize > 0 && (ByteArray.empty ++ block1).size > header.windowSize.toNat
       then (ByteArray.empty ++ block1).extract
         ((ByteArray.empty ++ block1).size - header.windowSize.toNat)
         (ByteArray.empty ++ block1).size
       else ByteArray.empty ++ block1)
      #[1, 4, 8] header.windowSize.toNat
      = .ok (blockOutput2, newHist2) := by
    simp only [ByteArray.empty_append]
    exact hexec2
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_rle_then_compressed_sequences data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
    block1 afterByte1
    hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
    llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2
    hoff hparse1 hbs1 hws1 htype1 hrle1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hNumSeq2 hfse2 hbbr2
    hdec2 hexec2' hlast2
  frame_from_blocks

end Zstd.Spec
