import Zstd.Spec.Succeeds

/-!
# Zstandard Frame Specification — Two-Compressed-Block Content

Frame-level content characterization theorems for two-block frames where
both blocks are compressed (homogeneous): two literals-only blocks, or
two sequences blocks.
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

/-! ## decompressFrame compressed two-block content -/

/-- When `decompressFrame` succeeds on a frame containing two compressed blocks
    (both with numSeq=0, i.e. literals only), the output equals `literals1 ++ literals2`.
    Lifts `decompressBlocksWF_two_compressed_literals_blocks` to frame level. -/
theorem decompressFrame_two_compressed_literals_blocks_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    -- Block 1 (non-last compressed, numSeq=0)
    (hdr1 : Zstd.Native.ZstdBlockHeader) (afterHdr1 : Nat)
    (literals1 : ByteArray) (afterLiterals1 : Nat)
    (huffTree1 : Option Zstd.Native.ZstdHuffmanTable)
    (modes1 : Zstd.Native.SequenceCompressionModes) (afterSeqHeader1 : Nat)
    -- Block 2 (last compressed, numSeq=0)
    (hdr2 : Zstd.Native.ZstdBlockHeader) (afterHdr2 : Nat)
    (literals2 : ByteArray) (afterLiterals2 : Nat)
    (huffTree2 : Option Zstd.Native.ZstdHuffmanTable)
    (modes2 : Zstd.Native.SequenceCompressionModes) (afterSeqHeader2 : Nat)
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
    -- Block 2 hypotheses (compressed, last)
    (hoff2 : ¬ data.size ≤ afterHdr1 + hdr1.blockSize.toNat)
    (hparse2 : Zstd.Native.parseBlockHeader data (afterHdr1 + hdr1.blockSize.toNat)
                 = .ok (hdr2, afterHdr2))
    (hbs2 : ¬ hdr2.blockSize > 131072)
    (hws2 : ¬ (header.windowSize > 0 && hdr2.blockSize.toUInt64 > header.windowSize))
    (htype2 : hdr2.blockType = .compressed)
    (hblockEnd2 : ¬ data.size < afterHdr2 + hdr2.blockSize.toNat)
    (hlit2 : Zstd.Native.parseLiteralsSection data afterHdr2
               (if let some ht := huffTree1 then some ht else none)
               = .ok (literals2, afterLiterals2, huffTree2))
    (hseq2 : Zstd.Native.parseSequencesHeader data afterLiterals2
               = .ok (0, modes2, afterSeqHeader2))
    (hlast2 : hdr2.lastBlock = true) :
    output = literals1 ++ literals2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Compute the exact block loop result using step + single-block theorems
  have hblocks : Zstd.Native.decompressBlocksWF data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8]
      = .ok (ByteArray.empty ++ literals1 ++ literals2,
             afterHdr2 + hdr2.blockSize.toNat) := by
    rw [decompressBlocksWF_compressed_literals_only_step data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1 literals1 afterLiterals1 huffTree1
      modes1 afterSeqHeader1 hoff hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1
      hnotlast1 hadv1]
    cases huffTree1 with
    | none =>
      exact decompressBlocksWF_single_compressed_literals_only data
        (afterHdr1 + hdr1.blockSize.toNat) header.windowSize (ByteArray.empty ++ literals1)
        none {} #[1, 4, 8]
        hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 modes2 afterSeqHeader2
        hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hlast2
    | some ht =>
      exact decompressBlocksWF_single_compressed_literals_only data
        (afterHdr1 + hdr1.blockSize.toNat) header.windowSize (ByteArray.empty ++ literals1)
        (some ht) {} #[1, 4, 8]
        hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 modes2 afterSeqHeader2
        hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2 hlit2 hseq2 hlast2
  frame_from_blocks

/-- When `decompressFrame` succeeds on a frame containing two compressed blocks
    (both with numSeq > 0, i.e. using sequences), the output equals
    `blockOutput1 ++ blockOutput2`. Block 2 receives the updated Huffman table,
    replaced FSE tables, updated offset history, and extended output from block 1.
    Lifts `decompressBlocksWF_two_compressed_sequences_blocks` to frame level.

    Inlines `decompressBlocksWF_compressed_sequences_step` +
    `decompressBlocksWF_single_compressed_sequences` at the frame level to avoid
    dependent-type mismatch with the composition theorem's Huffman threading. -/
theorem decompressFrame_two_compressed_sequences_blocks_content (data : ByteArray)
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
    (hfse2 : Zstd.Native.resolveSequenceFseTables modes2 data afterSeqHeader2
               { litLen := some llTable1, offset := some ofTable1, matchLen := some mlTable1 }
               = .ok (llTable2, ofTable2, mlTable2, afterTables2))
    (hbbr2 : Zstd.Native.BackwardBitReader.init data afterTables2
               (afterHdr2 + hdr2.blockSize.toNat) = .ok bbr2)
    (hdec2 : Zstd.Native.decodeSequences llTable2 ofTable2 mlTable2 bbr2 numSeq2
               = .ok sequences2)
    (hexec2 : Zstd.Native.executeSequences sequences2 literals2
                (if header.windowSize > 0 && blockOutput1.size > header.windowSize.toNat
                 then blockOutput1.extract (blockOutput1.size - header.windowSize.toNat)
                        blockOutput1.size
                 else blockOutput1)
                newHist1 header.windowSize.toNat
                = .ok (blockOutput2, newHist2))
    (hlast2 : hdr2.lastBlock = true) :
    output = blockOutput1 ++ blockOutput2 := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr1 afterHdr1 hparse1
  -- Bridge executeSequences for block 1: frame starts with empty output,
  -- so window check is trivial
  have hexec1' : Zstd.Native.executeSequences sequences1 literals1
      (if header.windowSize > 0 && ByteArray.empty.size > header.windowSize.toNat
       then ByteArray.empty.extract (ByteArray.empty.size - header.windowSize.toNat)
              ByteArray.empty.size
       else ByteArray.empty)
      #[1, 4, 8] header.windowSize.toNat
      = .ok (blockOutput1, newHist1) := by
    simp only [ByteArray.size_empty, Nat.not_lt_zero, decide_false, Bool.and_false]
    exact hexec1
  -- Bridge executeSequences for block 2: block-loop uses (ByteArray.empty ++ blockOutput1)
  -- as the window reference, convert to blockOutput1 directly
  have hexec2' : Zstd.Native.executeSequences sequences2 literals2
      (if header.windowSize > 0 &&
           (ByteArray.empty ++ blockOutput1).size > header.windowSize.toNat
       then (ByteArray.empty ++ blockOutput1).extract
              ((ByteArray.empty ++ blockOutput1).size - header.windowSize.toNat)
              (ByteArray.empty ++ blockOutput1).size
       else ByteArray.empty ++ blockOutput1)
      newHist1 header.windowSize.toNat
      = .ok (blockOutput2, newHist2) := by
    simp only [ByteArray.empty_append]
    exact hexec2
  -- Reduce block 1 (compSeq step) then apply block 2 (single compSeq).
  -- We inline the two-step proof to avoid dependent-type mismatch with the
  -- composition theorem's elaboration of `if let` in hlit2.
  have hblocks : Zstd.Native.decompressBlocksWF data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8]
      = .ok (ByteArray.empty ++ blockOutput1 ++ blockOutput2,
             afterHdr2 + hdr2.blockSize.toNat) := by
    rw [decompressBlocksWF_compressed_sequences_step data afterHeader header.windowSize
      ByteArray.empty none {} #[1, 4, 8] hdr1 afterHdr1
      literals1 afterLiterals1 huffTree1 numSeq1 modes1 afterSeqHeader1
      llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1 blockOutput1 newHist1
      hoff hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1 hNumSeq1 hfse1 hbbr1
      hdec1 hexec1' hnotlast1 hadv1]
    exact decompressBlocksWF_single_compressed_sequences data
      (afterHdr1 + hdr1.blockSize.toNat) header.windowSize (ByteArray.empty ++ blockOutput1)
      _ { litLen := some llTable1, offset := some ofTable1, matchLen := some mlTable1 }
      newHist1
      hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
      llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2
      hoff2 hparse2 hbs2 hws2 htype2 hblockEnd2
      (by cases huffTree1 <;> exact hlit2) hseq2 hNumSeq2 hfse2 hbbr2
      hdec2 hexec2' hlast2
  frame_from_blocks

end Zstd.Spec
