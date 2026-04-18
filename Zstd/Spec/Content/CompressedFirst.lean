import Zstd.Spec.Succeeds

/-!
# Zstandard Frame Specification — Compressed-First Two-Block Content

Frame-level content characterization theorems for two-block frames where
the first block is compressed (literals-only or sequences) followed by a
last block of any type (raw, RLE, or compressed).
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

/-- When `decompressFrame` succeeds and the frame contains a non-last compressed
    block with numSeq=0 (literals only) followed by a last raw block, the output
    equals `literals1 ++ block2`. Compressed-literals blocks don't modify FSE
    tables or offset history, and raw blocks don't use Huffman/FSE state, so no
    state threading complexity arises. -/
theorem decompressFrame_compressed_lit_then_raw_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last compressed, numSeq=0)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zstd.Native.ZstdHuffmanTable)
    (modes1 : Zstd.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    -- Block 2 (last raw)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterBlock2 : Nat)
    -- Frame hypotheses
    (hframe : Zstd.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zstd.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    -- Block 1 hypotheses (compressed, non-last)
    (hparse1 : Zstd.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zstd.Native.parseLiteralsSection data afterHdr1 none
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zstd.Native.parseSequencesHeader data afterLiterals1
               = .ok (0, modes1, afterSeqHeader1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterHdr1 + hdr1.blockSize.toNat ≤ afterHeader)
    -- Block 2 hypotheses (raw, last)
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zstd.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .raw)
    (hraw2 : Zstd.Native.decompressRawBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterBlock2))
    (hlast2 : hdr2.lastBlock = true) :
    output = literals1 ++ block2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_compressed_literals_then_raw data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
    literals1 afterLiterals1 huffTree1 modes1 afterSeqHeader1
    hdr2 afterHdr2 block2 afterBlock2
    hoff hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hraw2 hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a non-last compressed
    block with numSeq=0 (literals only) followed by a last RLE block, the output
    equals `literals1 ++ block2`. Compressed-literals blocks don't modify FSE
    tables or offset history, and RLE blocks don't use Huffman/FSE state, so no
    state threading complexity arises. -/
theorem decompressFrame_compressed_lit_then_rle_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last compressed, numSeq=0)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zstd.Native.ZstdHuffmanTable)
    (modes1 : Zstd.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    -- Block 2 (last RLE)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterByte2 : Nat)
    -- Frame hypotheses
    (hframe : Zstd.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zstd.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    -- Block 1 hypotheses (compressed, non-last)
    (hparse1 : Zstd.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zstd.Native.parseLiteralsSection data afterHdr1 none
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zstd.Native.parseSequencesHeader data afterLiterals1
               = .ok (0, modes1, afterSeqHeader1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterHdr1 + hdr1.blockSize.toNat ≤ afterHeader)
    -- Block 2 hypotheses (RLE, last)
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zstd.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .rle)
    (hrle2 : Zstd.Native.decompressRLEBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterByte2))
    (hlast2 : hdr2.lastBlock = true) :
    output = literals1 ++ block2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_compressed_literals_then_rle data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
    literals1 afterLiterals1 huffTree1 modes1 afterSeqHeader1
    hdr2 afterHdr2 block2 afterByte2
    hoff hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hrle2 hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a non-last compressed
    block with numSeq>0 (sequences) followed by a last raw block, the output
    equals `blockOutput1 ++ block2`. The compressed-sequences block produces
    `blockOutput1` via sequence execution; the raw block contributes `block2`
    directly. Raw blocks ignore all Huffman/FSE/offset state from block 1. -/
theorem decompressFrame_compressed_seq_then_raw_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last compressed, numSeq > 0)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zstd.Native.ZstdHuffmanTable)
    (numSeq1 : Nat) (modes1 : Zstd.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    (llTable1 ofTable1 mlTable1 : Zstd.Native.FseTable) (afterTables1 : Nat)
    (bbr1 : Zstd.Native.BackwardBitReader)
    (sequences1 : Array Zstd.Native.ZstdSequence)
    (blockOutput1 : ByteArray) (newHist1 : Array Nat)
    -- Block 2 (last raw)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterBlock2 : Nat)
    -- Frame hypotheses
    (hframe : Zstd.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zstd.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    -- Block 1 hypotheses (compressed, non-last, numSeq > 0)
    (hparse1 : Zstd.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zstd.Native.parseLiteralsSection data afterHdr1 none
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zstd.Native.parseSequencesHeader data afterLiterals1
               = .ok (numSeq1, modes1, afterSeqHeader1))
    (hNumSeq1 : ¬ numSeq1 == 0)
    (hfse1 : Zstd.Native.resolveSequenceFseTables modes1 data afterSeqHeader1 {}
               = .ok (llTable1, ofTable1, mlTable1, afterTables1))
    (hbbr1 : Zstd.Native.BackwardBitReader.init data afterTables1
               (afterHdr1 + hdr1.blockSize.toNat) = .ok bbr1)
    (hdec1 : Zstd.Native.decodeSequences llTable1 ofTable1 mlTable1 bbr1 numSeq1
               = .ok sequences1)
    (hexec1 : Zstd.Native.executeSequences sequences1 literals1 ByteArray.empty
                #[1, 4, 8] header.windowSize.toNat
                = .ok (blockOutput1, newHist1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ (afterHdr1 + hdr1.blockSize.toNat) ≤ afterHeader)
    -- Block 2 hypotheses (raw, last)
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zstd.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .raw)
    (hraw2 : Zstd.Native.decompressRawBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterBlock2))
    (hlast2 : hdr2.lastBlock = true) :
    output = blockOutput1 ++ block2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Bridge executeSequences: frame starts with empty output, so window check is trivial
  have hexec1' : Zstd.Native.executeSequences sequences1 literals1
      (if header.windowSize > 0 && ByteArray.empty.size > header.windowSize.toNat
       then ByteArray.empty.extract (ByteArray.empty.size - header.windowSize.toNat)
              ByteArray.empty.size
       else ByteArray.empty)
      #[1, 4, 8] header.windowSize.toNat
      = .ok (blockOutput1, newHist1) := by
    simp only [ByteArray.size_empty, Nat.not_lt_zero, decide_false, Bool.and_false]
    exact hexec1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_compressed_seq_then_raw data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
    literals1 afterLiterals1 huffTree1 numSeq1 modes1 afterSeqHeader1
    llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1 blockOutput1 newHist1
    hdr2 afterHdr2 block2 afterBlock2
    hoff hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hNumSeq1 hfse1 hbbr1
    hdec1 hexec1' hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hraw2 hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a non-last compressed
    block with numSeq>0 (sequences) followed by a last compressed block with
    numSeq=0 (literals only), the output equals `blockOutput1 ++ literals2`.
    Block 1 produces updated Huffman tree and FSE tables; block 2's
    `parseLiteralsSection` uses the potentially updated tree from block 1.

    Inlines `decompressBlocksWF_compressed_sequences_step` +
    `decompressBlocksWF_single_compressed_literals_only` at the frame level. -/
theorem decompressFrame_compressed_seq_then_compressed_lit_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last compressed, numSeq > 0)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zstd.Native.ZstdHuffmanTable)
    (numSeq1 : Nat) (modes1 : Zstd.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    (llTable1 ofTable1 mlTable1 : Zstd.Native.FseTable) (afterTables1 : Nat)
    (bbr1 : Zstd.Native.BackwardBitReader)
    (sequences1 : Array Zstd.Native.ZstdSequence)
    (blockOutput1 : ByteArray) (newHist1 : Array Nat)
    -- Block 2 (last compressed, numSeq=0)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zstd.Native.ZstdHuffmanTable)
    (modes2 : Zstd.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
    -- Frame hypotheses
    (hframe : Zstd.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zstd.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    -- Block 1 hypotheses (compressed, non-last, numSeq > 0)
    (hparse1 : Zstd.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zstd.Native.parseLiteralsSection data afterHdr1 none
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zstd.Native.parseSequencesHeader data afterLiterals1
               = .ok (numSeq1, modes1, afterSeqHeader1))
    (hNumSeq1 : ¬ numSeq1 == 0)
    (hfse1 : Zstd.Native.resolveSequenceFseTables modes1 data afterSeqHeader1 {}
               = .ok (llTable1, ofTable1, mlTable1, afterTables1))
    (hbbr1 : Zstd.Native.BackwardBitReader.init data afterTables1
               (afterHdr1 + hdr1.blockSize.toNat) = .ok bbr1)
    (hdec1 : Zstd.Native.decodeSequences llTable1 ofTable1 mlTable1 bbr1 numSeq1
               = .ok sequences1)
    (hexec1 : Zstd.Native.executeSequences sequences1 literals1 ByteArray.empty
                #[1, 4, 8] header.windowSize.toNat
                = .ok (blockOutput1, newHist1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ (afterHdr1 + hdr1.blockSize.toNat) ≤ afterHeader)
    -- Block 2 hypotheses (compressed, last, numSeq=0)
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zstd.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zstd.Native.parseLiteralsSection data afterHdr2 huffTree1
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zstd.Native.parseSequencesHeader data afterLiterals2
               = .ok (0, modes2, afterSeqHeader2))
    (hlast2 : hdr2.lastBlock = true) :
    output = blockOutput1 ++ literals2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- The block-loop theorem needs the executeSequences with window-checked output.
  -- Since decompressBlocks passes ByteArray.empty as initial output, and
  -- ByteArray.empty.size = 0 is never > windowSize.toNat, the window check
  -- simplifies to ByteArray.empty.
  have hexec1' : Zstd.Native.executeSequences sequences1 literals1
      (if header.windowSize > 0 && ByteArray.empty.size > header.windowSize.toNat
       then ByteArray.empty.extract (ByteArray.empty.size - header.windowSize.toNat)
              ByteArray.empty.size
       else ByteArray.empty)
      #[1, 4, 8] header.windowSize.toNat
      = .ok (blockOutput1, newHist1) := by
    simp only [ByteArray.size_empty, Nat.not_lt_zero, decide_false, Bool.and_false]
    exact hexec1
  -- Reduce block 1 (compSeq step) then apply block 2 (single compLit).
  -- We inline the two-step proof to avoid dependent-type mismatch with the
  -- composition theorem's elaboration of `if let` in hlit2.
  have hblocks : Zstd.Native.decompressBlocksWF data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8]
      = .ok (ByteArray.empty ++ blockOutput1 ++ literals2,
             afterHdr2 + hdr2.blockSize.toNat) := by
    rw [decompressBlocksWF_compressed_sequences_step data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
      literals1 afterLiterals1 huffTree1 numSeq1 modes1 afterSeqHeader1
      llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1 blockOutput1 newHist1
      hoff hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hNumSeq1 hfse1 hbbr1
      hdec1 hexec1' hnotlast1 hadv1]
    exact decompressBlocksWF_single_compressed_literals_only data
      (afterHdr1 + hdr1.blockSize.toNat) header.windowSize (ByteArray.empty ++ blockOutput1)
      _ { litLen := some llTable1, offset := some ofTable1, matchLen := some mlTable1 }
      newHist1
      hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 modes2 afterSeqHeader2
      hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2
      (by cases huffTree1 <;> exact hlit2) hseq2 hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a non-last compressed
    block with numSeq=0 (literals only) followed by a last compressed block with
    numSeq>0 (sequences), the output equals `literals1 ++ blockOutput2`.
    Block 1 produces updated Huffman tree; FSE tables and offset history are
    unchanged (numSeq=0). Block 2 uses the updated Huffman tree for
    `parseLiteralsSection`, the original FSE tables (`{}`) for
    `resolveSequenceFseTables`, and the original offset history.

    Inlines `decompressBlocksWF_compressed_literals_only_step` +
    `decompressBlocksWF_single_compressed_sequences` at the frame level. -/
theorem decompressFrame_compressed_lit_then_compressed_seq_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last compressed, numSeq=0)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zstd.Native.ZstdHuffmanTable)
    (modes1 : Zstd.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
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
    -- Block 1 hypotheses (compressed, non-last, numSeq=0)
    (hparse1 : Zstd.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zstd.Native.parseLiteralsSection data afterHdr1 none
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zstd.Native.parseSequencesHeader data afterLiterals1
               = .ok (0, modes1, afterSeqHeader1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ afterHdr1 + hdr1.blockSize.toNat ≤ afterHeader)
    -- Block 2 hypotheses (compressed, last, numSeq > 0)
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zstd.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zstd.Native.parseLiteralsSection data afterHdr2 huffTree1
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
                (if header.windowSize > 0 && literals1.size > header.windowSize.toNat
                 then literals1.extract (literals1.size - header.windowSize.toNat)
                        literals1.size
                 else literals1)
                #[1, 4, 8] header.windowSize.toNat
                = .ok (blockOutput2, newHist2))
    (hlast2 : hdr2.lastBlock = true) :
    output = literals1 ++ blockOutput2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- The block-loop theorem needs executeSequences with (output ++ literals1) as the
  -- window reference, where output = ByteArray.empty. Convert to use literals1 directly.
  have hexec2' : Zstd.Native.executeSequences sequences2 literals2
      (if header.windowSize > 0 &&
           (ByteArray.empty ++ literals1).size > header.windowSize.toNat
       then (ByteArray.empty ++ literals1).extract
              ((ByteArray.empty ++ literals1).size - header.windowSize.toNat)
              (ByteArray.empty ++ literals1).size
       else ByteArray.empty ++ literals1)
      #[1, 4, 8] header.windowSize.toNat
      = .ok (blockOutput2, newHist2) := by
    simp only [ByteArray.empty_append]
    exact hexec2
  -- Reduce block 1 (compLit step) then apply block 2 (single compSeq).
  -- We inline the two-step proof to avoid dependent-type mismatch with the
  -- composition theorem's elaboration of `if let` in hlit2.
  have hblocks : Zstd.Native.decompressBlocksWF data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8]
      = .ok (ByteArray.empty ++ literals1 ++ blockOutput2,
             afterHdr2 + hdr2.blockSize.toNat) := by
    rw [decompressBlocksWF_compressed_literals_only_step data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
      literals1 afterLiterals1 huffTree1 modes1 afterSeqHeader1
      hoff hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hnotlast1 hadv1]
    exact decompressBlocksWF_single_compressed_sequences data
      (afterHdr1 + hdr1.blockSize.toNat) header.windowSize (ByteArray.empty ++ literals1)
      _ {} #[1, 4, 8]
      hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
      llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2
      hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2
      (by cases huffTree1 <;> exact hlit2) hseq2 hNumSeq2 hfse2 hbbr2
      hdec2 hexec2' hlast2
  frame_from_blocks
/-- When `decompressBlocksWF` encounters a non-last compressed block with
    sequences (numSeq > 0) followed by a last RLE block, the output is
    `output ++ blockOutput1 ++ block2` at the position after the RLE byte.
    The RLE block doesn't use Huffman/FSE/history state — it just replicates
    a single byte.

    Composes `decompressBlocksWF_compressed_sequences_step` and
    `decompressBlocksWF_single_rle`. -/
theorem decompressBlocksWF_compressed_seq_then_rle (data : ByteArray)
    (off : Nat) (windowSize : UInt64) (output : ByteArray)
    (prevHuff : Option Zstd.Native.ZstdHuffmanTable)
    (prevFse : Zstd.Native.PrevFseTables) (history : Array Nat)
    -- Block 1 (non-last compressed, numSeq > 0)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zstd.Native.ZstdHuffmanTable)
    (numSeq1 : Nat) (modes1 : Zstd.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    (llTable1 ofTable1 mlTable1 : Zstd.Native.FseTable) (afterTables1 : Nat)
    (bbr1 : Zstd.Native.BackwardBitReader)
    (sequences1 : Array Zstd.Native.ZstdSequence)
    (blockOutput1 : ByteArray) (newHist1 : Array Nat)
    -- Block 2 (last RLE)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterByte2 : Nat)
    -- Block 1 hypotheses
    (hoff1 : ¬ data.size ≤ off)
    (hparse1 : Zstd.Native.parseBlockHeader data off = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (windowSize > 0 && hdr1.blockSize.toUInt64 > windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zstd.Native.parseLiteralsSection data afterHdr1 prevHuff
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zstd.Native.parseSequencesHeader data afterLiterals1
               = .ok (numSeq1, modes1, afterSeqHeader1))
    (hNumSeq1 : ¬ numSeq1 == 0)
    (hfse1 : Zstd.Native.resolveSequenceFseTables modes1 data afterSeqHeader1 prevFse
               = .ok (llTable1, ofTable1, mlTable1, afterTables1))
    (hbbr1 : Zstd.Native.BackwardBitReader.init data afterTables1
               (afterHdr1 + hdr1.blockSize.toNat) = .ok bbr1)
    (hdec1 : Zstd.Native.decodeSequences llTable1 ofTable1 mlTable1 bbr1 numSeq1
               = .ok sequences1)
    (hexec1 : Zstd.Native.executeSequences sequences1 literals1
                (if windowSize > 0 && output.size > windowSize.toNat
                 then output.extract (output.size - windowSize.toNat) output.size
                 else output)
                history windowSize.toNat
                = .ok (blockOutput1, newHist1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ (afterHdr1 + hdr1.blockSize.toNat) ≤ off)
    -- Block 2 hypotheses
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zstd.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (windowSize > 0 && hdr2.blockSize.toUInt64 > windowSize))
    (htype2 : hdr2.blockType = .rle)
    (hrle2 : Zstd.Native.decompressRLEBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterByte2))
    (hlast2 : hdr2.lastBlock = true) :
    Zstd.Native.decompressBlocksWF data off windowSize output prevHuff prevFse history
      = .ok (output ++ blockOutput1 ++ block2, afterByte2) := by
  rw [decompressBlocksWF_compressed_sequences_step data off windowSize output prevHuff
    prevFse history hdr1 afterHdr1 literals1 afterLiterals1 huffTree1 numSeq1 modes1
    afterSeqHeader1 llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1 blockOutput1
    newHist1 hoff1 hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hNumSeq1 hfse1 hbbr1
    hdec1 hexec1 hnotlast1 hadv1]
  exact decompressBlocksWF_single_rle data
    (afterHdr1 + hdr1.blockSize.toNat) windowSize (output ++ blockOutput1)
    _ { litLen := some llTable1, offset := some ofTable1, matchLen := some mlTable1 }
    newHist1
    hdr2 afterHdr2 block2 afterByte2
    hoff2 hparse2 hbs2 hws2 htype2 hrle2 hlast2

/-- When `decompressFrame` succeeds and the frame contains a non-last compressed
    block with numSeq>0 (sequences) followed by a last RLE block, the output
    equals `blockOutput1 ++ block2`. The compressed-sequences block produces
    `blockOutput1` via sequence execution; the RLE block contributes `block2`
    directly. RLE blocks ignore all Huffman/FSE/offset state from block 1. -/
theorem decompressFrame_compressed_seq_then_rle_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last compressed, numSeq > 0)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zstd.Native.ZstdHuffmanTable)
    (numSeq1 : Nat) (modes1 : Zstd.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    (llTable1 ofTable1 mlTable1 : Zstd.Native.FseTable) (afterTables1 : Nat)
    (bbr1 : Zstd.Native.BackwardBitReader)
    (sequences1 : Array Zstd.Native.ZstdSequence)
    (blockOutput1 : ByteArray) (newHist1 : Array Nat)
    -- Block 2 (last RLE)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (block2 : ByteArray) (afterByte2 : Nat)
    -- Frame hypotheses
    (hframe : Zstd.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zstd.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    -- Block 1 hypotheses (compressed, non-last, numSeq > 0)
    (hparse1 : Zstd.Native.parseBlockHeader data afterHeader = .ok (hdr1, afterHdr1))
    (hbs1 : ¬ hdr1.blockSize > 131072)
    (hws1 : ¬ (header.windowSize > 0 && hdr1.blockSize.toUInt64 > header.windowSize))
    (htype1 : hdr1.blockType = .compressed)
    (hblockEnd1 : ¬ data.size < afterHdr1 + hdr1.blockSize.toNat)
    (hlit1 : Zstd.Native.parseLiteralsSection data afterHdr1 none
               = .ok (literals1, afterLiterals1, huffTree1))
    (hseq1 : Zstd.Native.parseSequencesHeader data afterLiterals1
               = .ok (numSeq1, modes1, afterSeqHeader1))
    (hNumSeq1 : ¬ numSeq1 == 0)
    (hfse1 : Zstd.Native.resolveSequenceFseTables modes1 data afterSeqHeader1 {}
               = .ok (llTable1, ofTable1, mlTable1, afterTables1))
    (hbbr1 : Zstd.Native.BackwardBitReader.init data afterTables1
               (afterHdr1 + hdr1.blockSize.toNat) = .ok bbr1)
    (hdec1 : Zstd.Native.decodeSequences llTable1 ofTable1 mlTable1 bbr1 numSeq1
               = .ok sequences1)
    (hexec1 : Zstd.Native.executeSequences sequences1 literals1 ByteArray.empty
                #[1, 4, 8] header.windowSize.toNat
                = .ok (blockOutput1, newHist1))
    (hnotlast1 : hdr1.lastBlock = false)
    (hadv1 : ¬ (afterHdr1 + hdr1.blockSize.toNat) ≤ afterHeader)
    -- Block 2 hypotheses (RLE, last)
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zstd.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .rle)
    (hrle2 : Zstd.Native.decompressRLEBlock data afterHdr2 hdr2.blockSize
               = .ok (block2, afterByte2))
    (hlast2 : hdr2.lastBlock = true) :
    output = blockOutput1 ++ block2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Bridge executeSequences: frame starts with empty output, so window check is trivial
  have hexec1' : Zstd.Native.executeSequences sequences1 literals1
      (if header.windowSize > 0 && ByteArray.empty.size > header.windowSize.toNat
       then ByteArray.empty.extract (ByteArray.empty.size - header.windowSize.toNat)
              ByteArray.empty.size
       else ByteArray.empty)
      #[1, 4, 8] header.windowSize.toNat
      = .ok (blockOutput1, newHist1) := by
    simp only [ByteArray.size_empty, Nat.not_lt_zero, decide_false, Bool.and_false]
    exact hexec1
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_compressed_seq_then_rle data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
    literals1 afterLiterals1 huffTree1 numSeq1 modes1 afterSeqHeader1
    llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1 blockOutput1 newHist1
    hdr2 afterHdr2 block2 afterByte2
    hoff hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hNumSeq1 hfse1 hbbr1
    hdec1 hexec1' hnotlast1 hadv1
    hoff2 hparse2 hbs2 hws2 htype2 hrle2 hlast2
  frame_from_blocks

end Zstd.Spec
