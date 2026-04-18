import Zstd.Spec.Succeeds

/-!
# Zstandard Frame Specification — Single-Block Content

Frame-level content characterization theorems for frames containing a
single last compressed block (literals-only or sequences).
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

/-- When `decompressFrame` succeeds and the frame contains a single last
    compressed block with numSeq=0 (literals only), the output equals the
    literal section content. -/
theorem decompressFrame_single_compressed_literals_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hdr : Zstd.Native.ZstdBlockHeader) (afterHdr : Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zstd.Native.ZstdHuffmanTable)
    (modes : Zstd.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (hframe : Zstd.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zstd.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hparse : Zstd.Native.parseBlockHeader data afterHeader = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (header.windowSize > 0 && hdr.blockSize.toUInt64 > header.windowSize))
    (htype : hdr.blockType = .compressed)
    (hblockEnd : ¬ data.size < afterHdr + hdr.blockSize.toNat)
    (hlit : Zstd.Native.parseLiteralsSection data afterHdr none
              = .ok (literals, afterLiterals, huffTree))
    (hseq : Zstd.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader))
    (hlast : hdr.lastBlock = true) :
    output = literals := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr afterHdr hparse
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_single_compressed_literals_only data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr afterHdr
    literals afterLiterals huffTree modes afterSeqHeader
    hoff hparse hbs hws htype hblockEnd hlit hseq hlast
  frame_from_blocks

/-- When `decompressFrame` succeeds and the frame contains a single last
    compressed block with sequences (numSeq > 0), the output equals the
    sequence execution result. -/
theorem decompressFrame_single_compressed_sequences_content (data : ByteArray)
    (pos : Nat) (output : ByteArray) (pos' : Nat)
    (header : Zstd.Native.ZstdFrameHeader) (afterHeader : Nat)
    (hdr : Zstd.Native.ZstdBlockHeader) (afterHdr : Nat)
    (literals : ByteArray) (afterLiterals : Nat)
    (huffTree : Option Zstd.Native.ZstdHuffmanTable)
    (numSeq : Nat) (modes : Zstd.Native.SequenceCompressionModes) (afterSeqHeader : Nat)
    (llTable ofTable mlTable : Zstd.Native.FseTable) (afterTables : Nat)
    (bbr : Zstd.Native.BackwardBitReader)
    (sequences : Array Zstd.Native.ZstdSequence)
    (blockOutput : ByteArray) (newHist : Array Nat)
    (hframe : Zstd.Native.decompressFrame data pos = .ok (output, pos'))
    (hh : Zstd.Native.parseFrameHeader data pos = .ok (header, afterHeader))
    (hparse : Zstd.Native.parseBlockHeader data afterHeader = .ok (hdr, afterHdr))
    (hbs : ¬ hdr.blockSize > 131072)
    (hws : ¬ (header.windowSize > 0 && hdr.blockSize.toUInt64 > header.windowSize))
    (htype : hdr.blockType = .compressed)
    (hblockEnd : ¬ data.size < afterHdr + hdr.blockSize.toNat)
    (hlit : Zstd.Native.parseLiteralsSection data afterHdr none
              = .ok (literals, afterLiterals, huffTree))
    (hseq : Zstd.Native.parseSequencesHeader data afterLiterals
              = .ok (numSeq, modes, afterSeqHeader))
    (hNumSeq : ¬ numSeq == 0)
    (hfse : Zstd.Native.resolveSequenceFseTables modes data afterSeqHeader {}
              = .ok (llTable, ofTable, mlTable, afterTables))
    (hbbr : Zstd.Native.BackwardBitReader.init data afterTables
              (afterHdr + hdr.blockSize.toNat) = .ok bbr)
    (hdec : Zstd.Native.decodeSequences llTable ofTable mlTable bbr numSeq
              = .ok sequences)
    (hexec : Zstd.Native.executeSequences sequences literals ByteArray.empty
               #[1, 4, 8] header.windowSize.toNat
               = .ok (blockOutput, newHist))
    (hlast : hdr.lastBlock = true) :
    output = blockOutput := by
  have hoff := parseBlockHeader_data_not_le data afterHeader hdr afterHdr hparse
  -- The block-loop theorem needs the executeSequences with window-checked output.
  -- Since decompressBlocks passes ByteArray.empty as initial output, and
  -- ByteArray.empty.size = 0 is never > windowSize.toNat, the window check
  -- simplifies to ByteArray.empty.
  have hexec' : Zstd.Native.executeSequences sequences literals
      (if header.windowSize > 0 && ByteArray.empty.size > header.windowSize.toNat
       then ByteArray.empty.extract (ByteArray.empty.size - header.windowSize.toNat)
              ByteArray.empty.size
       else ByteArray.empty)
      #[1, 4, 8] header.windowSize.toNat
      = .ok (blockOutput, newHist) := by
    simp only [ByteArray.size_empty, Nat.not_lt_zero, decide_false, Bool.and_false]
    exact hexec
  -- Compute the exact block loop result
  have hblocks := decompressBlocksWF_single_compressed_sequences data afterHeader
    header.windowSize ByteArray.empty none {} #[1, 4, 8] hdr afterHdr
    literals afterLiterals huffTree numSeq modes afterSeqHeader
    llTable ofTable mlTable afterTables bbr sequences blockOutput newHist
    hoff hparse hbs hws htype hblockEnd hlit hseq hNumSeq hfse hbbr hdec hexec' hlast
  frame_from_blocks

end Zstd.Spec
