import Zstd.Native.Huffman
import Zstd.Spec.Huffman.Table

/-!
# Properties of `parseHuffmanTreeDescriptor`

Position-advancement and validity properties of the Huffman tree
descriptor parser, including the two weight-parsing helpers
(`parseHuffmanWeightsDirect`, `parseHuffmanWeightsFse`). The key
output-level theorems are `parseHuffmanTreeDescriptor_pos_ge_two`,
`parseHuffmanTreeDescriptor_le_size`, `parseHuffmanTreeDescriptor_valid`,
and `parseHuffmanTreeDescriptor_maxBits_pos`; they compose structural
bounds from the weight parsers with `buildZstdHuffmanTable_valid`.
-/

namespace Zstd.Spec.Huffman

open Zstd.Native (ZstdHuffmanTable)

open Zstd.Native in
/-- When `parseHuffmanWeightsDirect` succeeds, the returned position equals
    `pos + (numWeights + 1) / 2`. -/
private theorem parseHuffmanWeightsDirect_pos_eq (data : ByteArray) (pos numWeights : Nat)
    (weights : Array UInt8) (pos' : Nat)
    (h : parseHuffmanWeightsDirect data pos numWeights = .ok (weights, pos')) :
    pos' = pos + (numWeights + 1) / 2 := by
  simp only [parseHuffmanWeightsDirect, bind, Except.bind] at h
  split at h
  · exact nomatch h
  · split at h
    · exact nomatch h
    · simp only [pure, Pure.pure, Except.pure] at h
      split at h
      · exact nomatch h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact h.2.symm

open Zstd.Native in
/-- When `parseHuffmanWeightsFse` succeeds, the returned position equals
    `pos + 1 + compressedSize`. -/
private theorem parseHuffmanWeightsFse_pos_eq (data : ByteArray) (pos compressedSize : Nat)
    (weights : Array UInt8) (pos' : Nat)
    (h : parseHuffmanWeightsFse data pos compressedSize = .ok (weights, pos')) :
    pos' = pos + 1 + compressedSize := by
  simp only [parseHuffmanWeightsFse, bind, Except.bind] at h
  split at h
  · exact nomatch h
  · -- decodeFseDistribution
    split at h
    · exact nomatch h
    · -- buildFseTable
      split at h
      · exact nomatch h
      · -- BackwardBitReader.init
        split at h
        · exact nomatch h
        · -- decodeFseSymbolsAll
          split at h
          · exact nomatch h
          · split at h
            · exact nomatch h
            · obtain ⟨-, rfl⟩ := h
              rfl

open Zstd.Native in
/-- When `parseHuffmanWeightsDirect` succeeds, the returned position is within
    the data bounds: `pos' ≤ data.size`. -/
theorem parseHuffmanWeightsDirect_le_size (data : ByteArray) (pos numWeights : Nat)
    (weights : Array UInt8) (pos' : Nat)
    (h : parseHuffmanWeightsDirect data pos numWeights = .ok (weights, pos')) :
    pos' ≤ data.size := by
  have hpos := parseHuffmanWeightsDirect_pos_eq data pos numWeights weights pos' h
  simp only [parseHuffmanWeightsDirect, bind, Except.bind] at h
  split at h
  · exact nomatch h
  · rename_i hle
    rw [hpos]; omega

open Zstd.Native in
/-- When `parseHuffmanWeightsFse` succeeds, the returned position is within
    the data bounds: `pos' ≤ data.size`. -/
private theorem parseHuffmanWeightsFse_le_size (data : ByteArray) (pos compressedSize : Nat)
    (weights : Array UInt8) (pos' : Nat)
    (h : parseHuffmanWeightsFse data pos compressedSize = .ok (weights, pos')) :
    pos' ≤ data.size := by
  have hpos := parseHuffmanWeightsFse_pos_eq data pos compressedSize weights pos' h
  simp only [parseHuffmanWeightsFse, bind, Except.bind] at h
  split at h
  · exact nomatch h
  · rename_i hle
    rw [hpos]; omega

open Zstd.Native in
/-- Decompose a successful `parseHuffmanTreeDescriptor` call: extract the build
    success, position lower bound (`≥ pos + 2`), and position upper bound
    (`≤ data.size`). Both the direct and FSE paths call `buildZstdHuffmanTable`
    and produce a position that is bounded. This factors out the shared case
    analysis previously duplicated across `_pos_ge_two`, `_le_size`, and
    `_build_elim`. -/
private theorem parseHuffmanTreeDescriptor_ok_elim (data : ByteArray) (pos : Nat)
    (table : ZstdHuffmanTable) (pos' : Nat)
    (h : parseHuffmanTreeDescriptor data pos = .ok (table, pos')) :
    (∃ weights : Array UInt8, buildZstdHuffmanTable weights = .ok table) ∧
    pos' ≥ pos + 2 ∧ pos' ≤ data.size := by
  simp only [parseHuffmanTreeDescriptor, bind, Except.bind] at h
  by_cases h1 : data.size < pos + 1
  · rw [dif_pos h1] at h; exact nomatch h
  · rw [dif_neg h1] at h; simp only [pure, Pure.pure, Except.pure] at h
    have hpos_bound : pos < data.size := by omega
    by_cases h2 : (data[pos]'hpos_bound).toNat ≥ 128
    · rw [if_pos h2] at h
      cases hwd : parseHuffmanWeightsDirect data (pos + 1) ((data[pos]'hpos_bound).toNat - 127) with
      | error e => simp only [hwd] at h; exact nomatch h
      | ok v =>
        rw [hwd] at h; dsimp only [Bind.bind, Except.bind] at h
        cases hbt : buildZstdHuffmanTable v.fst with
        | error e => simp only [hbt] at h; exact nomatch h
        | ok t =>
          rw [hbt] at h; dsimp only [pure, Pure.pure, Except.pure] at h
          have hpos := parseHuffmanWeightsDirect_pos_eq data (pos + 1)
            ((data[pos]'hpos_bound).toNat - 127) v.fst v.snd hwd
          have hle := parseHuffmanWeightsDirect_le_size data (pos + 1)
            ((data[pos]'hpos_bound).toNat - 127) v.fst v.snd hwd
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨⟨v.fst, hbt⟩, by rw [hpos]; omega, hle⟩
    · rw [if_neg (show ¬(data[pos]'hpos_bound).toNat ≥ 128 from h2)] at h
      by_cases h3 : ((data[pos]'hpos_bound).toNat == 0) = true
      · rw [if_pos h3] at h; exact nomatch h
      · rw [if_neg h3] at h
        cases hfse : parseHuffmanWeightsFse data pos (data[pos]'hpos_bound).toNat with
        | error e => simp only [hfse] at h; exact nomatch h
        | ok v =>
          rw [hfse] at h; dsimp only [Bind.bind, Except.bind] at h
          cases hbt : buildZstdHuffmanTable v.fst with
          | error e => simp only [hbt] at h; exact nomatch h
          | ok t =>
            rw [hbt] at h; dsimp only [pure, Pure.pure, Except.pure] at h
            have hpos := parseHuffmanWeightsFse_pos_eq data pos
              (data[pos]'hpos_bound).toNat v.fst v.snd hfse
            have hle := parseHuffmanWeightsFse_le_size data pos
              (data[pos]'hpos_bound).toNat v.fst v.snd hfse
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨⟨v.fst, hbt⟩, by rw [hpos]; simp only [beq_iff_eq] at h3; omega, hle⟩

open Zstd.Native in
/-- When `parseHuffmanTreeDescriptor` succeeds, the returned position is at least
    `pos + 2` (1 header byte + at least 1 data byte). -/
theorem parseHuffmanTreeDescriptor_pos_ge_two (data : ByteArray) (pos : Nat)
    (table : ZstdHuffmanTable) (pos' : Nat)
    (h : parseHuffmanTreeDescriptor data pos = .ok (table, pos')) :
    pos' ≥ pos + 2 :=
  (parseHuffmanTreeDescriptor_ok_elim data pos table pos' h).2.1

open Zstd.Native in
/-- When `parseHuffmanTreeDescriptor` succeeds, the returned position is strictly
    greater than the input position. -/
theorem parseHuffmanTreeDescriptor_pos_gt (data : ByteArray) (pos : Nat)
    (table : ZstdHuffmanTable) (pos' : Nat)
    (h : parseHuffmanTreeDescriptor data pos = .ok (table, pos')) :
    pos' > pos := by
  have := (parseHuffmanTreeDescriptor_ok_elim data pos table pos' h).2.1; omega

open Zstd.Native in
/-- When `parseHuffmanTreeDescriptor` succeeds, the returned position is within
    the data bounds: `pos' ≤ data.size`. -/
theorem parseHuffmanTreeDescriptor_le_size (data : ByteArray) (pos : Nat)
    (table : ZstdHuffmanTable) (pos' : Nat)
    (h : parseHuffmanTreeDescriptor data pos = .ok (table, pos')) :
    pos' ≤ data.size :=
  (parseHuffmanTreeDescriptor_ok_elim data pos table pos' h).2.2

open Zstd.Native in
/-- When `parseHuffmanTreeDescriptor` succeeds, the returned table satisfies
    `ValidHuffmanTable`. Both the direct and FSE paths call `buildZstdHuffmanTable`,
    which guarantees validity. -/
theorem parseHuffmanTreeDescriptor_valid (data : ByteArray) (pos : Nat)
    (table : ZstdHuffmanTable) (pos' : Nat)
    (h : parseHuffmanTreeDescriptor data pos = .ok (table, pos')) :
    ValidHuffmanTable table.table table.maxBits := by
  obtain ⟨weights, hbt⟩ := (parseHuffmanTreeDescriptor_ok_elim data pos table pos' h).1
  exact buildZstdHuffmanTable_valid weights table hbt

open Zstd.Native in
/-- When `parseHuffmanTreeDescriptor` succeeds, the table has `maxBits ≥ 1`.
    This follows from `buildZstdHuffmanTable_maxBits_pos`. -/
theorem parseHuffmanTreeDescriptor_maxBits_pos (data : ByteArray) (pos : Nat)
    (table : ZstdHuffmanTable) (pos' : Nat)
    (h : parseHuffmanTreeDescriptor data pos = .ok (table, pos')) :
    0 < table.maxBits := by
  obtain ⟨weights, hbt⟩ := (parseHuffmanTreeDescriptor_ok_elim data pos table pos' h).1
  exact buildZstdHuffmanTable_maxBits_pos weights table hbt

end Zstd.Spec.Huffman
