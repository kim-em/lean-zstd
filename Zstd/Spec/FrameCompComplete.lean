import Zstd.Spec.FrameBase

/-!
# Zstandard Top-Level Decompressor — Compressed-First Composed Completeness

Composed completeness theorems for `decompressZstd` with compressed-first block
layouts. This covers:

- Single compressed-block frames (zero-seq and with-sequences)
- Two-block frames whose first block is compressed

See `Zstd.Spec.FrameBase` for foundation lemmas and
`Zstd.Spec.FrameSimpleComplete` for the raw/RLE-first analogue. -/

namespace Zstd.Spec.ZstdFrame

/-! ## decompressZstd composed completeness for compressed blocks -/

/-- End-to-end composed completeness for a single compressed-block frame with zero
    sequences (literals only): byte-level conditions on the frame header, block header,
    and parsing conditions imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_single_compressed_zero_seq` (header + block → frame success)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success)

    Header field constraints and block conditions are universally quantified over
    `(hdr, afterHdr)` from `parseFrameHeader`, since the caller doesn't know these
    values without parsing. -/
theorem decompressZstd_succeeds_single_compressed_zero_seq_frame (data : ByteArray)
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
    -- Block conditions at afterHdr (compressed block: type=2, lastBlock=1)
    (htypeVal : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
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
    (hblockEnd : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Literals section and sequences header succeed (quantified, with existentials)
    (hparsing : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ∃ literals afterLiterals huffTree modes afterSeqHeader,
            Zstd.Native.parseLiteralsSection data (afterHdr + 3) none
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
  -- Step 2: Specialize universally quantified hypotheses
  have htypeVal' := htypeVal hdr afterHdr hparse
  have hlastBit' := hlastBit hdr afterHdr hparse
  have hblockSizeBound' := hblockSizeBound hdr afterHdr hparse
  have hwindow' := hwindow hdr afterHdr hparse
  have hblockEnd' := hblockEnd hdr afterHdr hparse
  -- Step 3: Obtain literals and sequences parsing from combined hypothesis
  obtain ⟨literals, afterLiterals, huffTree, modes, afterSeqHeader, hlit', hseq'⟩ :=
    hparsing hdr afterHdr hparse
  -- Step 4: Apply decompressFrame_succeeds_single_compressed_zero_seq
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_single_compressed_zero_seq
    data 0 hdr afterHdr literals afterLiterals huffTree modes afterSeqHeader
    hparse (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
    (hnosize hdr afterHdr hparse) (by omega) htypeVal' hlastBit' hblockSizeBound'
    hwindow' hblockEnd' hlit' hseq'
  -- Step 5: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-- End-to-end composed completeness for a single compressed-block frame with sequences
    (numSeq > 0): byte-level conditions on the frame header, block header, and full
    parsing/decoding/execution pipeline imply `decompressZstd` succeeds.

    Same structure as `decompressZstd_succeeds_single_compressed_zero_seq_frame` but
    with additional conditions for FSE table resolution, backward bitstream
    initialization, sequence decoding, and sequence execution.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_single_compressed_sequences` (header + block + sequences → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_single_compressed_sequences_frame (data : ByteArray)
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
    -- Block conditions at afterHdr (compressed block: type=2, lastBlock=1)
    (htypeVal : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
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
    (hblockEnd : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Full parsing/decoding/execution pipeline (quantified, with existentials)
    (hparsing : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ∃ literals afterLiterals huffTree numSeq modes afterSeqHeader
            llTable ofTable mlTable afterTables bbr sequences blockOutput newHist,
            Zstd.Native.parseLiteralsSection data (afterHdr + 3) none
              = .ok (literals, afterLiterals, huffTree) ∧
            Zstd.Native.parseSequencesHeader data afterLiterals
              = .ok (numSeq, modes, afterSeqHeader) ∧
            ¬ (numSeq == 0) ∧
            Zstd.Native.resolveSequenceFseTables modes data afterSeqHeader {}
              = .ok (llTable, ofTable, mlTable, afterTables) ∧
            Zstd.Native.BackwardBitReader.init data afterTables
              (afterHdr + 3 + (((data[afterHdr]!.toUInt32
                ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
                ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
              = .ok bbr ∧
            Zstd.Native.decodeSequences llTable ofTable mlTable bbr numSeq
              = .ok sequences ∧
            Zstd.Native.executeSequences sequences literals ByteArray.empty #[1, 4, 8]
              hdr.windowSize.toNat = .ok (blockOutput, newHist))
    -- Frame terminates the data
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
  have hblockEnd' := hblockEnd hdr afterHdr hparse
  -- Step 3: Obtain full pipeline from combined hypothesis
  obtain ⟨literals, afterLiterals, huffTree, numSeq, modes, afterSeqHeader,
    llTable, ofTable, mlTable, afterTables, bbr, sequences, blockOutput, newHist,
    hlit', hseq', hNumSeq', hfse', hbbr', hdec', hexec'⟩ := hparsing hdr afterHdr hparse
  -- Step 4: Apply decompressFrame_succeeds_single_compressed_sequences
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_single_compressed_sequences
    data 0 hdr afterHdr literals afterLiterals huffTree numSeq modes afterSeqHeader
    llTable ofTable mlTable afterTables bbr sequences blockOutput newHist
    hparse (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
    (hnosize hdr afterHdr hparse) (by omega) htypeVal' hlastBit' hblockSizeBound'
    hwindow' hblockEnd' hlit' hseq' hNumSeq' hfse' hbbr' hdec' hexec'
  -- Step 5: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-! ## decompressZstd two-block composed completeness (comp_zero_seq first block) -/

/-- End-to-end composed completeness for a frame with a non-last compressed block
    (numSeq=0) followed by a last raw block: byte-level conditions on the frame header,
    both block headers, and the compressed block's literals/sequences parsing
    imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_compressed_zero_seq_then_raw` (header + compressed + raw → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_compressed_zero_seq_then_raw_frame (data : ByteArray)
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
    -- Block 1 (non-last compressed, zero sequences) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
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
    (hblockEnd1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Literals section and sequences header succeed for block 1
    (hparsing1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ∃ literals afterLiterals huffTree modes afterSeqHeader,
            Zstd.Native.parseLiteralsSection data (afterHdr + 3) none
              = .ok (literals, afterLiterals, huffTree) ∧
            Zstd.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader))
    -- Block 2 (last raw) at off2 = afterHdr + 3 + blockSize1
    (hsize2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)]!.toUInt32
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 2]!.toUInt32 <<< 16))
            >>> 1) &&& 3 = 0)
    (hlastBit2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)]!.toUInt32
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 2]!.toUInt32 <<< 16))
            &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)]!.toUInt32
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 2]!.toUInt32 <<< 16))
            >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)]!.toUInt32
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 2]!.toUInt32 <<< 16))
            >>> 3).toUInt64 > hdr.windowSize))
    (hpayload2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) + 3 +
            (((data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)]!.toUInt32
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 2]!.toUInt32 <<< 16))
            >>> 3).toNat))
    -- Frame terminates the data
    (hterm : ∀ content pos', Zstd.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zstd.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Obtain literals and sequences parsing from combined hypothesis
  obtain ⟨literals, afterLiterals, huffTree, modes, afterSeqHeader, hlit1', hseq1'⟩ :=
    hparsing1 hdr afterHdr hparse
  -- Step 3: Apply decompressFrame_succeeds_compressed_zero_seq_then_raw
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_compressed_zero_seq_then_raw
    data 0 hdr afterHdr literals afterLiterals huffTree modes afterSeqHeader hparse
    (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse) (hnosize hdr afterHdr hparse)
    (hsize1 hdr afterHdr hparse) (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse)
    (hblockEnd1 hdr afterHdr hparse) hlit1' hseq1'
    _ rfl
    (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse) (hlastBit2 hdr afterHdr hparse)
    (hblockSize2 hdr afterHdr hparse) (hwindow2 hdr afterHdr hparse)
    (hpayload2 hdr afterHdr hparse)
  -- Step 4: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-- End-to-end composed completeness for a frame with a non-last compressed block
    (numSeq=0) followed by a last RLE block: byte-level conditions on the frame header,
    both block headers, and the compressed block's literals/sequences parsing
    imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_compressed_zero_seq_then_rle` (header + compressed + RLE → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_compressed_zero_seq_then_rle_frame (data : ByteArray)
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
    -- Block 1 (non-last compressed, zero sequences) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
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
    (hblockEnd1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Literals section and sequences header succeed for block 1
    (hparsing1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ∃ literals afterLiterals huffTree modes afterSeqHeader,
            Zstd.Native.parseLiteralsSection data (afterHdr + 3) none
              = .ok (literals, afterLiterals, huffTree) ∧
            Zstd.Native.parseSequencesHeader data afterLiterals
              = .ok (0, modes, afterSeqHeader))
    -- Block 2 (last RLE) at off2 = afterHdr + 3 + blockSize1
    (hsize2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) + 3)
    (htypeVal2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)]!.toUInt32
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 2]!.toUInt32 <<< 16))
            >>> 1) &&& 3 = 1)
    (hlastBit2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)]!.toUInt32
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 2]!.toUInt32 <<< 16))
            &&& 1 = 1)
    (hblockSize2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)]!.toUInt32
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 2]!.toUInt32 <<< 16))
            >>> 3) ≤ 131072)
    (hwindow2 : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ¬ (hdr.windowSize > 0 &&
            ((data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)]!.toUInt32
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat) + 2]!.toUInt32 <<< 16))
            >>> 3).toUInt64 > hdr.windowSize))
    (hpayload2 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ (afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)) + 4)
    -- Frame terminates the data
    (hterm : ∀ content pos', Zstd.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zstd.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Obtain literals and sequences parsing from combined hypothesis
  obtain ⟨literals, afterLiterals, huffTree, modes, afterSeqHeader, hlit1', hseq1'⟩ :=
    hparsing1 hdr afterHdr hparse
  -- Step 3: Apply decompressFrame_succeeds_compressed_zero_seq_then_rle
  obtain ⟨content, pos', hframe⟩ := Zstd.Spec.decompressFrame_succeeds_compressed_zero_seq_then_rle
    data 0 hdr afterHdr literals afterLiterals huffTree modes afterSeqHeader hparse
    (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse) (hnosize hdr afterHdr hparse)
    (hsize1 hdr afterHdr hparse) (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse)
    (hblockEnd1 hdr afterHdr hparse) hlit1' hseq1'
    _ rfl
    (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse) (hlastBit2 hdr afterHdr hparse)
    (hblockSize2 hdr afterHdr hparse) (hwindow2 hdr afterHdr hparse)
    (hpayload2 hdr afterHdr hparse)
  -- Step 4: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-! ## decompressZstd two-block composed completeness (comp_zero_seq first, compressed second) -/

/-- End-to-end composed completeness for a frame with a non-last compressed block
    (numSeq=0) followed by a last compressed block (numSeq=0): byte-level conditions
    on the frame header and both block headers, plus a combined parsing hypothesis
    for both blocks' literals/sequences, imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_compressed_zero_seq_then_compressed_zero_seq` (header + two compressed → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_compressed_zero_seq_then_compressed_zero_seq_frame (data : ByteArray)
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
    -- Block 1 (non-last compressed, zero sequences) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
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
    (hblockEnd1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last compressed, zero sequences) at off2
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
    -- Combined parsing for both blocks (block 2 inherits Huffman table from block 1)
    (hparsing : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ∃ literals1 afterLiterals1 huffTree1 modes1 afterSeqHeader1
          literals2 afterLiterals2 huffTree2 modes2 afterSeqHeader2,
          Zstd.Native.parseLiteralsSection data (afterHdr + 3) none
            = .ok (literals1, afterLiterals1, huffTree1) ∧
          Zstd.Native.parseSequencesHeader data afterLiterals1
            = .ok (0, modes1, afterSeqHeader1) ∧
          Zstd.Native.parseLiteralsSection data (off2 + 3)
            (if let some ht := huffTree1 then some ht else none)
            = .ok (literals2, afterLiterals2, huffTree2) ∧
          Zstd.Native.parseSequencesHeader data afterLiterals2
            = .ok (0, modes2, afterSeqHeader2))
    -- Frame terminates the data
    (hterm : ∀ content pos', Zstd.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zstd.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Obtain literals and sequences parsing from combined hypothesis
  obtain ⟨literals1, afterLiterals1, huffTree1, modes1, afterSeqHeader1,
          literals2, afterLiterals2, huffTree2, modes2, afterSeqHeader2,
          hlit1', hseq1', hlit2', hseq2'⟩ :=
    hparsing hdr afterHdr hparse
  -- Step 3: Case-split on huffTree1 to resolve dependent match, then apply frame-level theorem
  cases huffTree1 <;> (
    obtain ⟨content, pos', hframe⟩ :=
      Zstd.Spec.decompressFrame_succeeds_compressed_zero_seq_then_compressed_zero_seq
      data 0 hdr afterHdr
      literals1 afterLiterals1 _ modes1 afterSeqHeader1
      literals2 afterLiterals2 huffTree2 modes2 afterSeqHeader2
      hparse (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
      (hnosize hdr afterHdr hparse) (hsize1 hdr afterHdr hparse)
      (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
      (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse)
      (hblockEnd1 hdr afterHdr hparse) hlit1' hseq1'
      _ rfl (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse)
      (hlastBit2 hdr afterHdr hparse) (hblockSize2 hdr afterHdr hparse)
      (hwindow2 hdr afterHdr hparse) (hblockEnd2 hdr afterHdr hparse) hlit2' hseq2'
    -- Step 4: Apply decompressZstd_single_frame
    exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩)

/-- End-to-end composed completeness for a frame with a non-last compressed block
    (numSeq=0) followed by a last compressed block with sequences (numSeq > 0):
    byte-level conditions on the frame header and both block headers, plus a combined
    parsing/decoding/execution hypothesis for both blocks, imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_compressed_zero_seq_then_compressed_sequences` (header + compressed + compressed → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_compressed_zero_seq_then_compressed_sequences_frame (data : ByteArray)
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
    -- Block 1 (non-last compressed, zero sequences) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
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
    (hblockEnd1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Block 2 (last compressed, with sequences) at off2
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
    -- Combined parsing for both blocks: block 1 (zero_seq) + block 2 (full sequence pipeline)
    (hparsing : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr) →
        let off2 := afterHdr + 3 + (((data[afterHdr]!.toUInt32
              ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat)
        ∃ literals1 afterLiterals1 huffTree1 modes1 afterSeqHeader1
          literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
          llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2,
          Zstd.Native.parseLiteralsSection data (afterHdr + 3) none
            = .ok (literals1, afterLiterals1, huffTree1) ∧
          Zstd.Native.parseSequencesHeader data afterLiterals1
            = .ok (0, modes1, afterSeqHeader1) ∧
          Zstd.Native.parseLiteralsSection data (off2 + 3)
            (if let some ht := huffTree1 then some ht else none)
            = .ok (literals2, afterLiterals2, huffTree2) ∧
          Zstd.Native.parseSequencesHeader data afterLiterals2
            = .ok (numSeq2, modes2, afterSeqHeader2) ∧
          ¬ (numSeq2 == 0) ∧
          Zstd.Native.resolveSequenceFseTables modes2 data afterSeqHeader2 {}
            = .ok (llTable2, ofTable2, mlTable2, afterTables2) ∧
          Zstd.Native.BackwardBitReader.init data afterTables2
            (off2 + 3 + (((data[off2]!.toUInt32
              ||| (data[off2 + 1]!.toUInt32 <<< 8)
              ||| (data[off2 + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
            = .ok bbr2 ∧
          Zstd.Native.decodeSequences llTable2 ofTable2 mlTable2 bbr2 numSeq2
            = .ok sequences2 ∧
          Zstd.Native.executeSequences sequences2 literals2
            (if hdr.windowSize > 0 &&
                  (ByteArray.empty ++ literals1).size > hdr.windowSize.toNat
              then (ByteArray.empty ++ literals1).extract
                ((ByteArray.empty ++ literals1).size - hdr.windowSize.toNat)
                (ByteArray.empty ++ literals1).size
              else (ByteArray.empty ++ literals1))
            #[1, 4, 8] hdr.windowSize.toNat
            = .ok (blockOutput2, newHist2))
    -- Frame terminates the data
    (hterm : ∀ content pos', Zstd.Native.decompressFrame data 0 = .ok (content, pos')
        → pos' ≥ data.size) :
    ∃ output, Zstd.Native.decompressZstd data = .ok output := by
  -- Step 1: Obtain header from parseFrameHeader_succeeds
  obtain ⟨hdr, afterHdr, hparse⟩ :=
    Zstd.Spec.parseFrameHeader_succeeds data 0 hmagic (by simpa only [Nat.zero_add] using hframeSize)
  -- Step 2: Obtain full pipeline from combined hypothesis
  obtain ⟨literals1, afterLiterals1, huffTree1, modes1, afterSeqHeader1,
          literals2, afterLiterals2, huffTree2, numSeq2, modes2, afterSeqHeader2,
          llTable2, ofTable2, mlTable2, afterTables2, bbr2, sequences2, blockOutput2, newHist2,
          hlit1', hseq1', hlit2', hseq2', hNumSeq2', hfse2', hbbr2', hdec2', hexec2'⟩ :=
    hparsing hdr afterHdr hparse
  -- Step 3: Case-split on huffTree1 to resolve dependent match, then apply frame-level theorem
  cases huffTree1 <;> (
    obtain ⟨content, pos', hframe⟩ :=
      Zstd.Spec.decompressFrame_succeeds_compressed_zero_seq_then_compressed_sequences
      data 0 hdr afterHdr
      literals1 afterLiterals1 _ modes1 afterSeqHeader1
      literals2 afterLiterals2 huffTree2 numSeq2 modes2 afterSeqHeader2
      llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2 blockOutput2 newHist2
      hparse (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
      (hnosize hdr afterHdr hparse) (hsize1 hdr afterHdr hparse)
      (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
      (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse)
      (hblockEnd1 hdr afterHdr hparse) hlit1' hseq1'
      _ rfl (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse)
      (hlastBit2 hdr afterHdr hparse) (hblockSize2 hdr afterHdr hparse)
      (hwindow2 hdr afterHdr hparse) (hblockEnd2 hdr afterHdr hparse) hlit2' hseq2'
      hNumSeq2' hfse2' hbbr2' hdec2' hexec2'
    -- Step 4: Apply decompressZstd_single_frame
    exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩)

/-! ## decompressZstd two-block composed completeness (comp_sequences first, raw/RLE second) -/

/-- End-to-end composed completeness for a frame with a non-last compressed block
    with sequences (numSeq > 0) followed by a last raw block: byte-level conditions
    on the frame header, block 1's full parsing/decoding/execution pipeline, and
    block 2's raw block conditions imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_compressed_sequences_then_raw` (header + compressed + raw → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_compressed_sequences_then_raw_frame (data : ByteArray)
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
    -- Block 1 (non-last compressed, numSeq > 0) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
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
    (hblockEnd1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Full parsing/decoding/execution pipeline for block 1 (quantified, with existentials)
    (hpipeline1 : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ∃ literals afterLiterals huffTree numSeq modes afterSeqHeader
            llTable ofTable mlTable afterTables bbr sequences blockOutput newHist,
            Zstd.Native.parseLiteralsSection data (afterHdr + 3) none
              = .ok (literals, afterLiterals, huffTree) ∧
            Zstd.Native.parseSequencesHeader data afterLiterals
              = .ok (numSeq, modes, afterSeqHeader) ∧
            ¬ (numSeq == 0) ∧
            Zstd.Native.resolveSequenceFseTables modes data afterSeqHeader {}
              = .ok (llTable, ofTable, mlTable, afterTables) ∧
            Zstd.Native.BackwardBitReader.init data afterTables
              (afterHdr + 3 + (((data[afterHdr]!.toUInt32
                ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
                ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
              = .ok bbr ∧
            Zstd.Native.decodeSequences llTable ofTable mlTable bbr numSeq
              = .ok sequences ∧
            Zstd.Native.executeSequences sequences literals ByteArray.empty
              #[1, 4, 8] hdr.windowSize.toNat = .ok (blockOutput, newHist))
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
  -- Step 2: Destructure pipeline existential for block 1
  obtain ⟨literals, afterLiterals, huffTree, numSeq, modes, afterSeqHeader,
    llTable, ofTable, mlTable, afterTables, bbr, sequences, blockOutput1, newHist1,
    hlit1', hseq1', hNumSeq1', hfse1', hbbr1', hdec1', hexec1'⟩ :=
    hpipeline1 hdr afterHdr hparse
  -- Step 3: Convert hexec1' to match block-level form (if-guard simplifies for empty output)
  have hexec1'' : Zstd.Native.executeSequences sequences literals
      (if hdr.windowSize > 0 && ByteArray.empty.size > hdr.windowSize.toNat
       then ByteArray.empty.extract (ByteArray.empty.size - hdr.windowSize.toNat)
         ByteArray.empty.size
       else ByteArray.empty)
      #[1, 4, 8] hdr.windowSize.toNat = .ok (blockOutput1, newHist1) := by
    simp only [ByteArray.size_empty, Nat.not_lt_zero, decide_false, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte]; exact hexec1'
  -- Step 4: Apply decompressFrame_succeeds_compressed_sequences_then_raw
  obtain ⟨content, pos', hframe⟩ :=
    Zstd.Spec.decompressFrame_succeeds_compressed_sequences_then_raw
    data 0 hdr afterHdr literals afterLiterals huffTree numSeq modes afterSeqHeader
    llTable ofTable mlTable afterTables bbr sequences blockOutput1 newHist1
    hparse (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
    (hnosize hdr afterHdr hparse) (hsize1 hdr afterHdr hparse)
    (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse)
    (hblockEnd1 hdr afterHdr hparse) hlit1' hseq1' hNumSeq1'
    hfse1' hbbr1' hdec1' hexec1''
    _ rfl (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse)
    (hlastBit2 hdr afterHdr hparse) (hblockSize2 hdr afterHdr hparse)
    (hwindow2 hdr afterHdr hparse) (hpayload2 hdr afterHdr hparse)
  -- Step 5: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-- End-to-end composed completeness for a frame with a non-last compressed block
    with sequences (numSeq > 0) followed by a last RLE block: byte-level conditions
    on the frame header, block 1's full parsing/decoding/execution pipeline, and
    block 2's RLE block conditions imply `decompressZstd` succeeds.

    Composes the full chain:
    1. `parseFrameHeader_succeeds` (byte-level magic + size → frame header parsed)
    2. `decompressFrame_succeeds_compressed_sequences_then_rle` (header + compressed + RLE → frame)
    3. `decompressZstd_single_frame` (frame success + end-of-data → API success) -/
theorem decompressZstd_succeeds_compressed_sequences_then_rle_frame (data : ByteArray)
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
    -- Block 1 (non-last compressed, numSeq > 0) at afterHdr
    (hsize1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3)
    (htypeVal1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → ((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
            ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 1) &&& 3 = 2)
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
    (hblockEnd1 : ∀ _hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (_hdr, afterHdr)
        → data.size ≥ afterHdr + 3 +
            (((data[afterHdr]!.toUInt32 ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
              ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
    -- Full parsing/decoding/execution pipeline for block 1 (quantified, with existentials)
    (hpipeline1 : ∀ hdr afterHdr, Zstd.Native.parseFrameHeader data 0 = .ok (hdr, afterHdr)
        → ∃ literals afterLiterals huffTree numSeq modes afterSeqHeader
            llTable ofTable mlTable afterTables bbr sequences blockOutput newHist,
            Zstd.Native.parseLiteralsSection data (afterHdr + 3) none
              = .ok (literals, afterLiterals, huffTree) ∧
            Zstd.Native.parseSequencesHeader data afterLiterals
              = .ok (numSeq, modes, afterSeqHeader) ∧
            ¬ (numSeq == 0) ∧
            Zstd.Native.resolveSequenceFseTables modes data afterSeqHeader {}
              = .ok (llTable, ofTable, mlTable, afterTables) ∧
            Zstd.Native.BackwardBitReader.init data afterTables
              (afterHdr + 3 + (((data[afterHdr]!.toUInt32
                ||| (data[afterHdr + 1]!.toUInt32 <<< 8)
                ||| (data[afterHdr + 2]!.toUInt32 <<< 16)) >>> 3).toNat))
              = .ok bbr ∧
            Zstd.Native.decodeSequences llTable ofTable mlTable bbr numSeq
              = .ok sequences ∧
            Zstd.Native.executeSequences sequences literals ByteArray.empty
              #[1, 4, 8] hdr.windowSize.toNat = .ok (blockOutput, newHist))
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
  -- Step 2: Destructure pipeline existential for block 1
  obtain ⟨literals, afterLiterals, huffTree, numSeq, modes, afterSeqHeader,
    llTable, ofTable, mlTable, afterTables, bbr, sequences, blockOutput1, newHist1,
    hlit1', hseq1', hNumSeq1', hfse1', hbbr1', hdec1', hexec1'⟩ :=
    hpipeline1 hdr afterHdr hparse
  -- Step 3: Convert hexec1' to match block-level form (if-guard simplifies for empty output)
  have hexec1'' : Zstd.Native.executeSequences sequences literals
      (if hdr.windowSize > 0 && ByteArray.empty.size > hdr.windowSize.toNat
       then ByteArray.empty.extract (ByteArray.empty.size - hdr.windowSize.toNat)
         ByteArray.empty.size
       else ByteArray.empty)
      #[1, 4, 8] hdr.windowSize.toNat = .ok (blockOutput1, newHist1) := by
    simp only [ByteArray.size_empty, Nat.not_lt_zero, decide_false, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte]; exact hexec1'
  -- Step 4: Apply decompressFrame_succeeds_compressed_sequences_then_rle
  obtain ⟨content, pos', hframe⟩ :=
    Zstd.Spec.decompressFrame_succeeds_compressed_sequences_then_rle
    data 0 hdr afterHdr literals afterLiterals huffTree numSeq modes afterSeqHeader
    llTable ofTable mlTable afterTables bbr sequences blockOutput1 newHist1
    hparse (hnodict hdr afterHdr hparse) (hnocksum hdr afterHdr hparse)
    (hnosize hdr afterHdr hparse) (hsize1 hdr afterHdr hparse)
    (htypeVal1 hdr afterHdr hparse) (hlastBit1 hdr afterHdr hparse)
    (hblockSize1 hdr afterHdr hparse) (hwindow1 hdr afterHdr hparse)
    (hblockEnd1 hdr afterHdr hparse) hlit1' hseq1' hNumSeq1'
    hfse1' hbbr1' hdec1' hexec1''
    _ rfl (hsize2 hdr afterHdr hparse) (htypeVal2 hdr afterHdr hparse)
    (hlastBit2 hdr afterHdr hparse) (hblockSize2 hdr afterHdr hparse)
    (hwindow2 hdr afterHdr hparse) (hpayload2 hdr afterHdr hparse)
  -- Step 5: Apply decompressZstd_single_frame
  exact ⟨content, decompressZstd_single_frame data content pos' hframe (hterm content pos' hframe)⟩

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (first non-last compressed with numSeq>0, second last compressed with
    numSeq=0), `decompressZstd` succeeds.  Derived from
    `decompressZstd_compressed_seq_then_compressed_lit_content`. -/
theorem decompressZstd_succeeds_compressed_sequences_then_compressed_zero_seq_frame
    (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
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
    (hframe : Zstd.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zstd.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    ∃ out, Zstd.Native.decompressZstd data = .ok out :=
  ⟨_, decompressZstd_compressed_seq_then_compressed_lit_content data output pos'
    header afterHeader hdr1 afterHdr1 literals1 afterLiterals1 huffTree1
    numSeq1 modes1 afterSeqHeader1 llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1
    blockOutput1 newHist1 hdr2 afterHdr2 literals2 afterLiterals2 huffTree2 modes2
    afterSeqHeader2 hframe hh hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1
    hNumSeq1 hfse1 hbbr1 hdec1 hexec1 hnotlast1 hadv1 hoff2 hparse2 hbs2 hws2 htype2
    hblockEnd2 hlit2 hseq2 hlast2 hend⟩

/-- When the input contains exactly one standard Zstd frame at position 0 with two
    blocks (both compressed with numSeq>0), `decompressZstd` succeeds.  Derived from
    `decompressZstd_two_compressed_sequences_blocks_content`. -/
theorem decompressZstd_succeeds_two_compressed_sequences_frame (data : ByteArray)
    (output : ByteArray) (pos' : Nat)
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
    (hframe : Zstd.Native.decompressFrame data 0 = .ok (output, pos'))
    (hh : Zstd.Native.parseFrameHeader data 0 = .ok (header, afterHeader))
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
    (hlast2 : hdr2.lastBlock = true)
    -- End of data
    (hend : pos' ≥ data.size) :
    ∃ out, Zstd.Native.decompressZstd data = .ok out :=
  ⟨_, decompressZstd_two_compressed_sequences_blocks_content data output pos'
    header afterHeader hdr1 afterHdr1 literals1 afterLiterals1 huffTree1
    numSeq1 modes1 afterSeqHeader1 llTable1 ofTable1 mlTable1 afterTables1 bbr1 sequences1
    blockOutput1 newHist1 hdr2 afterHdr2 literals2 afterLiterals2 huffTree2
    numSeq2 modes2 afterSeqHeader2 llTable2 ofTable2 mlTable2 afterTables2 bbr2 sequences2
    blockOutput2 newHist2 hframe hh hparse1 hbs1 hws1 htype1 hblockEnd1 hlit1 hseq1
    hNumSeq1 hfse1 hbbr1 hdec1 hexec1 hnotlast1 hadv1 hoff2 hparse2 hbs2 hws2 htype2
    hblockEnd2 hlit2 hseq2 hNumSeq2 hfse2 hbbr2 hdec2 hexec2 hlast2 hend⟩
end Zstd.Spec.ZstdFrame
