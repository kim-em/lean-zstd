import Zstd.Native.Huffman
import Zstd.Spec.Fse
import Zstd.Spec.Huffman.TreeDescriptor

/-!
# Parsing completeness theorems for the Huffman specification

These "*`_succeeds`*" theorems establish that, under the appropriate
precondition bundles, each parser returns `.ok`. They cover
`parseCompressedLiteralsHeader`, the four `parseLiteralsSection`
variants (raw / RLE / compressed / treeless), the two weight parsers
(`parseHuffmanWeightsDirect`, `parseHuffmanWeightsFse`), and the top-level
`parseHuffmanTreeDescriptor` in both direct and FSE modes.

Two small `def`s — `rawLiteralsSectionSize` and `rleLiteralsSectionMinSize`
— package the variable-width byte budgets needed by the raw / RLE
completeness theorems.
-/

namespace Zstd.Spec.Huffman

open Zstd.Native (ZstdHuffmanTable)
open ZipCommon (BitReader)

/-! ## Parsing completeness -/

open Zstd.Native in
/-- When `data` has enough bytes for the compressed literals header (3, 4, or 5 bytes
    depending on `sizeFormat`), `parseCompressedLiteralsHeader` always succeeds. -/
theorem parseCompressedLiteralsHeader_succeeds (data : ByteArray) (pos sizeFormat : Nat)
    (hsize : data.size ≥ pos + if sizeFormat ≤ 1 then 3 else if sizeFormat = 2 then 4 else 5) :
    ∃ regenSize compSize headerBytes fourStreams,
      parseCompressedLiteralsHeader data pos sizeFormat =
        .ok (regenSize, compSize, headerBytes, fourStreams) := by
  simp only [parseCompressedLiteralsHeader, pure, Except.pure]
  split
  · -- sizeFormat ≤ 1: needs 3 bytes
    rename_i hsf
    have hge : data.size ≥ pos + 3 := by rw [if_pos hsf] at hsize; exact hsize
    simp only [show pos + 3 ≤ data.size from by omega, ↓reduceDIte]
    exact ⟨_, _, _, _, rfl⟩
  · split
    · -- sizeFormat = 2: needs 4 bytes
      rename_i hnsf hsf2
      have hge : data.size ≥ pos + 4 := by
        have : sizeFormat = 2 := by rwa [beq_iff_eq] at hsf2
        rw [if_neg hnsf, if_pos this] at hsize; exact hsize
      simp only [show pos + 4 ≤ data.size from by omega, ↓reduceDIte]
      exact ⟨_, _, _, _, rfl⟩
    · -- sizeFormat ≥ 3: needs 5 bytes
      rename_i hnsf hnsf2
      have hge : data.size ≥ pos + 5 := by
        have : ¬(sizeFormat = 2) := by rwa [beq_iff_eq] at hnsf2
        rw [if_neg hnsf, if_neg this] at hsize; exact hsize
      simp only [show pos + 5 ≤ data.size from by omega, ↓reduceDIte]
      exact ⟨_, _, _, _, rfl⟩

open Zstd.Native in
/-- When litType = 3 (treeless), a previous Huffman table is available, the compressed
    header parses successfully, there is enough data for the payload, and Huffman decoding
    succeeds, `parseLiteralsSection` succeeds with the exact output determined by these
    parameters. -/
theorem parseLiteralsSection_succeeds_treeless (data : ByteArray) (pos : Nat)
    (huffTable : ZstdHuffmanTable)
    (regenSize compSize headerBytes : Nat) (fourStreams : Bool) (result : ByteArray)
    (hlit : (data[pos]! &&& 3).toNat = 3)
    (hpos : data.size ≥ pos + 1)
    (hparse : parseCompressedLiteralsHeader data pos ((data[pos]! >>> 2) &&& 3).toNat
              = .ok (regenSize, compSize, headerBytes, fourStreams))
    (hdata : data.size ≥ pos + headerBytes + compSize)
    (hdecode : decodeHuffmanLiterals huffTable data (pos + headerBytes)
                compSize regenSize fourStreams = .ok result) :
    parseLiteralsSection data pos (some huffTable) =
      .ok (result, pos + headerBytes + compSize, some huffTable) := by
  simp only [parseLiteralsSection, bind, Except.bind, pure, Except.pure]
  split
  · -- data.size < pos + 1 → absurd
    exfalso; omega
  · -- past size guard
    split
    · -- litType > 3 → absurd since litType = 3
      exfalso; omega
    · -- litType ≤ 3
      split
      · -- litType == 2 || litType == 3 → compressed/treeless path
        simp only [hparse]
        split
        · -- litType == 3 → treeless path
          simp only [show ¬(data.size < pos + headerBytes + compSize) from by omega,
            ↓reduceIte, hdecode]
        · -- litType ≠ 3 → absurd since hlit says litType = 3
          rename_i hne
          simp only [beq_iff_eq] at hne
          omega
      · -- litType ≠ 2 and ≠ 3 → absurd since hlit says litType = 3
        rename_i _ hne
        simp only [beq_iff_eq, Bool.or_eq_true, not_or] at hne
        omega

open Zstd.Native in
/-- When litType = 2 (compressed with new Huffman tree), there is enough data,
    the compressed header parses, `parseHuffmanTreeDescriptor` succeeds, the tree
    fits within the compressed data, and Huffman decoding succeeds,
    `parseLiteralsSection` succeeds with the exact output. The `prevHuffTree`
    parameter is universally quantified — litType=2 never uses it. -/
theorem parseLiteralsSection_succeeds_compressed (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (huffTable : ZstdHuffmanTable) (afterTree : Nat)
    (regenSize compSize headerBytes : Nat) (fourStreams : Bool) (result : ByteArray)
    (hlit : (data[pos]! &&& 3).toNat = 2)
    (hpos : data.size ≥ pos + 1)
    (hparse : parseCompressedLiteralsHeader data pos ((data[pos]! >>> 2) &&& 3).toNat
              = .ok (regenSize, compSize, headerBytes, fourStreams))
    (hdata : data.size ≥ pos + headerBytes + compSize)
    (htree : parseHuffmanTreeDescriptor data (pos + headerBytes)
             = .ok (huffTable, afterTree))
    (htreeSize : afterTree - (pos + headerBytes) ≤ compSize)
    (hdecode : decodeHuffmanLiterals huffTable data afterTree
                (compSize - (afterTree - (pos + headerBytes)))
                regenSize fourStreams = .ok result) :
    parseLiteralsSection data pos prevHuffTree =
      .ok (result, pos + headerBytes + compSize, some huffTable) := by
  simp only [parseLiteralsSection, bind, Except.bind, pure, Except.pure]
  split
  · -- data.size < pos + 1 → absurd
    exfalso; omega
  · -- past size guard
    split
    · -- litType > 3 → absurd since litType = 2
      exfalso; omega
    · -- litType ≤ 3
      split
      · -- litType == 2 || litType == 3 → compressed/treeless path
        simp only [hparse]
        split
        · -- litType == 3 → absurd since hlit says litType = 2
          rename_i heq3
          simp only [beq_iff_eq] at heq3
          omega
        · -- litType ≠ 3 → compressed path (our case)
          simp only [show ¬(data.size < pos + headerBytes + compSize) from by omega,
            ↓reduceIte, Except.mapError, htree,
            show ¬(afterTree - (pos + headerBytes) > compSize) from by omega,
            hdecode]
      · -- litType ≠ 2 and ≠ 3 → absurd since hlit says litType = 2
        rename_i _ hne
        simp only [beq_iff_eq, Bool.or_eq_true, not_or] at hne
        omega

private theorem forIn'_loop_always_ok' {α β ε : Type}
    (as curr : List α) (init : β)
    (f : α → β → Except ε (ForInStep β))
    (h_ok : ∀ a b, ∃ r, f a b = .ok r)
    (hsuf : ∃ bs, bs ++ curr = as) :
    ∃ result, List.forIn'.loop as (fun a _ b => f a b) curr init hsuf = .ok result := by
  induction curr generalizing init with
  | nil => exact ⟨init, rfl⟩
  | cons x xs ih =>
    unfold List.forIn'.loop
    dsimp only [Bind.bind, Except.bind]
    obtain ⟨r, hr⟩ := h_ok x init
    rw [hr]
    cases r with
    | done b' => exact ⟨b', rfl⟩
    | yield b' => exact ih b' _

private theorem forIn_range_always_ok' {β ε : Type} (n : Nat) (init : β)
    (f : Nat → β → Except ε (ForInStep β))
    (h_ok : ∀ i b, ∃ r, f i b = .ok r) :
    ∃ result, forIn [:n] init f = .ok result := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact forIn'_loop_always_ok' _ _ init (fun a b => f a b) h_ok _

open Zstd.Native in
/-- When `data` has enough bytes for the nibble-packed weight data,
    `parseHuffmanWeightsDirect` always succeeds. -/
theorem parseHuffmanWeightsDirect_succeeds (data : ByteArray) (pos numWeights : Nat)
    (hsize : data.size ≥ pos + (numWeights + 1) / 2) :
    ∃ weights afterPos,
      parseHuffmanWeightsDirect data pos numWeights = .ok (weights, afterPos) := by
  simp only [parseHuffmanWeightsDirect, bind, Except.bind, pure, Except.pure,
    show ¬(data.size < pos + (numWeights + 1) / 2) from by omega, ↓reduceIte]
  -- The forIn loop body always returns .ok (.yield _), so the loop succeeds
  suffices h : ∃ result, (forIn [:(numWeights + 1) / 2] (#[] : Array UInt8) fun i r =>
      Except.ok (ForInStep.yield ((r.push (data[pos + i]! >>> 4)).push (data[pos + i]! &&& 15))))
    = .ok result by
    obtain ⟨result, hr⟩ := h
    rw [hr]
    exact ⟨_, _, rfl⟩
  exact forIn_range_always_ok' _ _ _ (fun i (b : Array UInt8) =>
    ⟨ForInStep.yield ((b.push (data[pos + i]! >>> 4)).push (data[pos + i]! &&& 15)), rfl⟩)

open Zstd.Native in
/-- When data has enough bytes for the FSE-compressed weight range and
    each sub-call (`decodeFseDistribution`, `buildFseTable`,
    `BackwardBitReader.init`, `decodeFseSymbolsAll`) succeeds,
    `parseHuffmanWeightsFse` succeeds and returns the decoded weights
    with position advanced past the compressed range. -/
theorem parseHuffmanWeightsFse_succeeds
    (data : ByteArray) (pos compressedSize : Nat)
    (hsize : data.size ≥ pos + 1 + compressedSize)
    (probs : Array Int32) (accuracyLog : Nat) (br1 : BitReader)
    (hfse : decodeFseDistribution ⟨data, pos + 1, 0⟩ 256 6 = .ok (probs, accuracyLog, br1))
    (table : FseTable)
    (hbuild : buildFseTable probs accuracyLog = .ok table)
    (bbr : BackwardBitReader)
    (hinit : BackwardBitReader.init data br1.alignToByte.pos (pos + 1 + compressedSize) = .ok bbr)
    (weights : Array UInt8) (bbr' : BackwardBitReader)
    (hdecode : decodeFseSymbolsAll table bbr = .ok (weights, bbr')) :
    parseHuffmanWeightsFse data pos compressedSize =
      .ok (weights, pos + 1 + compressedSize) := by
  simp only [parseHuffmanWeightsFse, bind, Except.bind, pure, Except.pure,
    show ¬(data.size < pos + 1 + compressedSize) from by omega, ↓reduceIte,
    hfse, hbuild, hinit, hdecode]

open Zstd.Native in
/-- When the header byte indicates direct mode (≥ 128), data has enough bytes
    for the header and weight nibbles, and `buildZstdHuffmanTable` succeeds on
    the parsed weights, `parseHuffmanTreeDescriptor` succeeds. -/
theorem parseHuffmanTreeDescriptor_succeeds_direct (data : ByteArray) (pos : Nat)
    (hsize : data.size ≥ pos + 1)
    (hheader : data[pos]!.toNat ≥ 128)
    (hweights : data.size ≥ pos + 1 + ((data[pos]!.toNat - 127 + 1) / 2))
    (hbuild : ∀ weights afterPos,
      parseHuffmanWeightsDirect data (pos + 1) (data[pos]!.toNat - 127) = .ok (weights, afterPos) →
      ∃ table, buildZstdHuffmanTable weights = .ok table) :
    ∃ table afterPos,
      parseHuffmanTreeDescriptor data pos = .ok (table, afterPos) := by
  rw [getElem!_pos data pos (by omega)] at hheader hweights hbuild
  simp only [parseHuffmanTreeDescriptor, bind, Except.bind, pure, Except.pure,
    show ¬(data.size < pos + 1) from by omega, dite_false,
    show (data[pos]'(by omega)).toNat ≥ 128 from hheader]
  -- Chain: parseHuffmanWeightsDirect succeeds, then buildZstdHuffmanTable succeeds
  obtain ⟨weights, afterPos, hw⟩ :=
    parseHuffmanWeightsDirect_succeeds data (pos + 1) ((data[pos]'(by omega)).toNat - 127) (by omega)
  simp only [hw]
  obtain ⟨table, ht⟩ := hbuild weights afterPos hw
  simp only [ht]
  exact ⟨_, _, rfl⟩

open Zstd.Native in
/-- When the header byte indicates FSE mode (1..127), `parseHuffmanWeightsFse`
    succeeds, and `buildZstdHuffmanTable` succeeds on the decoded weights,
    `parseHuffmanTreeDescriptor` succeeds. -/
theorem parseHuffmanTreeDescriptor_succeeds_fse (data : ByteArray) (pos : Nat)
    (hsize : data.size ≥ pos + 1)
    (hbyte_pos : data[pos]!.toNat > 0)
    (hbyte_fse : data[pos]!.toNat < 128)
    (weights : Array UInt8) (afterWeights : Nat)
    (hweights : parseHuffmanWeightsFse data pos data[pos]!.toNat = .ok (weights, afterWeights))
    (huffTable : ZstdHuffmanTable)
    (htable : buildZstdHuffmanTable weights = .ok huffTable) :
    parseHuffmanTreeDescriptor data pos = .ok (huffTable, afterWeights) := by
  rw [getElem!_pos data pos (by omega)] at hbyte_pos hbyte_fse hweights
  simp only [parseHuffmanTreeDescriptor, bind, Except.bind, pure, Except.pure,
    show ¬(data.size < pos + 1) from by omega, dite_false,
    show ¬((data[pos]'(by omega)).toNat ≥ 128) from by omega]
  have h0 : ((data[pos]'(by omega)).toNat == 0) = false := by rw [beq_eq_false_iff_ne]; omega
  simp only [h0, Bool.false_eq_true, ↓reduceIte, hweights, htable]

/-! ## Parsing completeness (raw/RLE) -/

open Zstd.Native in
/-- Compute the total bytes needed for a raw literals section (litType = 0):
    variable-width header bytes plus `regenSize` payload bytes.
    The header size and regenerated size are extracted from the data bytes at `pos`. -/
def rawLiteralsSectionSize (data : ByteArray) (pos : Nat) : Nat :=
  if ((data[pos]! >>> 2 &&& 3).toNat == 0 || (data[pos]! >>> 2 &&& 3).toNat == 2) then
    1 + (data[pos]! >>> 3).toNat
  else if ((data[pos]! >>> 2 &&& 3).toNat == 1) then
    2 + ((data[pos]! >>> 4).toNat ||| (data[pos + 1]!.toNat <<< 4))
  else
    3 + ((data[pos]! >>> 4).toNat ||| (data[pos + 1]!.toNat <<< 4) ||| (data[pos + 2]!.toNat <<< 12))

open Zstd.Native in
/-- Compute the minimum bytes needed for an RLE literals section (litType = 1):
    variable-width header bytes plus 1 byte for the RLE value.
    Unlike raw literals, the payload is always exactly 1 byte regardless of `regenSize`. -/
def rleLiteralsSectionMinSize (data : ByteArray) (pos : Nat) : Nat :=
  if ((data[pos]! >>> 2 &&& 3).toNat == 0 || (data[pos]! >>> 2 &&& 3).toNat == 2) then 2
  else if ((data[pos]! >>> 2 &&& 3).toNat == 1) then 3
  else 4

open Zstd.Native in
/-- When litType = 0 (raw) and the data has enough bytes for the variable-width
    header plus `regenSize` payload bytes, `parseLiteralsSection` succeeds. -/
theorem parseLiteralsSection_succeeds_raw (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (hlit : (data[pos]! &&& 3).toNat = 0)
    (hsize : data.size ≥ pos + rawLiteralsSectionSize data pos) :
    ∃ literals pos' huffTable,
      parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable) := by
  -- Match on the result to avoid unfolding parseLiteralsSection under existentials
  match hresult : parseLiteralsSection data pos prevHuffTree with
  | .ok (lit, pos', ht) => exact ⟨lit, pos', ht, rfl⟩
  | .error _ =>
    exfalso
    simp only [parseLiteralsSection, bind, Except.bind, pure, Except.pure] at hresult
    split at hresult
    · -- data.size < pos + 1
      have : rawLiteralsSectionSize data pos ≥ 1 := by
        unfold rawLiteralsSectionSize
        split
        · omega
        · split <;> omega
      omega
    · split at hresult
      · omega -- litType > 3 contradicts hlit
      · split at hresult
        · rename_i _ hcomp -- litType == 2 || 3 contradicts hlit
          simp only [beq_iff_eq, Bool.or_eq_true] at hcomp; omega
        · -- raw/RLE path: sizeFormat case split
          split at hresult
          · -- sizeFormat == 0 || sizeFormat == 2
            rename_i hsf
            simp only [rawLiteralsSectionSize, hsf, ↓reduceIte] at hsize
            split at hresult
            · split at hresult
              · omega
              · exact nomatch hresult
            · -- litType ≠ 0 contradicts hlit
              simp only [beq_iff_eq] at *; omega
          · split at hresult
            · -- sizeFormat == 1
              unfold rawLiteralsSectionSize at hsize
              split at hsize
              · contradiction
              · -- sf1: hsize auto-resolved to concrete form
                split at hresult
                · omega
                · split at hresult
                  · split at hresult
                    · omega
                    · exact nomatch hresult
                  · simp only [beq_iff_eq] at *; omega
            · -- sizeFormat == 3
              unfold rawLiteralsSectionSize at hsize
              split at hsize
              · contradiction
              · -- sf3: hsize auto-resolved to concrete form
                split at hresult
                · omega
                · split at hresult
                  · split at hresult
                    · omega
                    · exact nomatch hresult
                  · simp only [beq_iff_eq] at *; omega

open Zstd.Native in
/-- When litType = 1 (RLE) and the data has enough bytes for the variable-width
    header plus 1 byte for the repeated value, `parseLiteralsSection` succeeds. -/
theorem parseLiteralsSection_succeeds_rle (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (hlit : (data[pos]! &&& 3).toNat = 1)
    (hsize : data.size ≥ pos + rleLiteralsSectionMinSize data pos) :
    ∃ literals pos' huffTable,
      parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable) := by
  match hresult : parseLiteralsSection data pos prevHuffTree with
  | .ok (lit, pos', ht) => exact ⟨lit, pos', ht, rfl⟩
  | .error _ =>
    exfalso
    simp only [parseLiteralsSection, bind, Except.bind, pure, Except.pure] at hresult
    split at hresult
    · -- data.size < pos + 1
      have : rleLiteralsSectionMinSize data pos ≥ 2 := by
        unfold rleLiteralsSectionMinSize
        split
        · omega
        · split <;> omega
      omega
    · split at hresult
      · omega -- litType > 3 contradicts hlit
      · split at hresult
        · rename_i _ hcomp -- litType == 2 || 3 contradicts hlit
          simp only [beq_iff_eq, Bool.or_eq_true] at hcomp; omega
        · -- raw/RLE path: sizeFormat case split
          split at hresult
          · -- sizeFormat == 0 || sizeFormat == 2
            rename_i hsf
            simp only [rleLiteralsSectionMinSize, hsf, ↓reduceIte] at hsize
            split at hresult
            · -- litType == 0 contradicts hlit
              simp only [beq_iff_eq] at *; omega
            · split at hresult
              · omega
              · exact nomatch hresult
          · split at hresult
            · -- sizeFormat == 1
              unfold rleLiteralsSectionMinSize at hsize
              split at hsize
              · contradiction
              · -- sf1: hsize auto-resolved to concrete form (= 3)
                split at hresult
                · omega -- header guard: data.size < pos + 2 contradicts hsize
                · split at hresult
                  · simp only [beq_iff_eq] at *; omega -- litType == 0 contradicts hlit
                  · split at hresult
                    · omega
                    · exact nomatch hresult
            · -- sizeFormat == 3
              unfold rleLiteralsSectionMinSize at hsize
              split at hsize
              · contradiction
              · -- sf3: hsize auto-resolved to concrete form (= 4)
                split at hresult
                · omega -- header guard: data.size < pos + 3 contradicts hsize
                · split at hresult
                  · simp only [beq_iff_eq] at *; omega -- litType == 0 contradicts hlit
                  · split at hresult
                    · omega
                    · exact nomatch hresult

end Zstd.Spec.Huffman
