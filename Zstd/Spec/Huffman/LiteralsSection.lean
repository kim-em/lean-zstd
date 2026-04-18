import Zstd.Native.Huffman

/-!
# Properties of `parseCompressedLiteralsHeader` and `parseLiteralsSection`

This module collects the structural and content properties of the two
literals-header parsers used in a Zstd compressed block:

* `parseCompressedLiteralsHeader_*`: `headerBytes` ≥ 3, correct header size
  per `sizeFormat`, correct `fourStreams` bit, `regen ≤ 0x3FFFF`.
* `parseLiteralsSection_*`: position advancement and `le data.size` bounds
  for each literal type (raw/RLE/compressed/treeless), plus content-shape
  guarantees for the raw and RLE types (contiguous slice / constant byte).
-/

namespace Zstd.Spec.Huffman

open Zstd.Native (ZstdHuffmanTable)

/-! ## parseCompressedLiteralsHeader properties -/

open Zstd.Native in
/-- `parseCompressedLiteralsHeader` always returns `headerBytes ≥ 3`. -/
private theorem parseCompressedLiteralsHeader_headerBytes_ge (data : ByteArray)
    (pos sizeFormat regen comp hdr : Nat) (fs : Bool)
    (h : parseCompressedLiteralsHeader data pos sizeFormat = .ok (regen, comp, hdr, fs)) :
    hdr ≥ 3 := by
  simp only [parseCompressedLiteralsHeader, pure, Except.pure] at h
  split at h
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
    · exact nomatch h
  · split at h
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
      · exact nomatch h
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h; omega
      · exact nomatch h

open Zstd.Native in
/-- `parseCompressedLiteralsHeader` returns the correct `headerSize` for each `sizeFormat`:
    `sizeFormat ≤ 1 → 3`, `sizeFormat = 2 → 4`, `sizeFormat > 2 → 5`. -/
theorem parseCompressedLiteralsHeader_headerSize (data : ByteArray) (pos : Nat)
    (sizeFormat : Nat) (regen comp headerSize : Nat) (fourStreams : Bool)
    (h : parseCompressedLiteralsHeader data pos sizeFormat
         = .ok (regen, comp, headerSize, fourStreams)) :
    (sizeFormat ≤ 1 → headerSize = 3) ∧
    (sizeFormat = 2 → headerSize = 4) ∧
    (sizeFormat > 2 → headerSize = 5) := by
  simp only [parseCompressedLiteralsHeader, pure, Except.pure] at h
  split at h
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, hhdr, -⟩ := h
      exact ⟨fun _ => by omega, fun _ => by omega, fun _ => by omega⟩
    · exact nomatch h
  · split at h
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        simp only [beq_iff_eq] at *
        obtain ⟨-, -, hhdr, -⟩ := h
        exact ⟨fun _ => by omega, fun _ => by omega, fun _ => by omega⟩
      · exact nomatch h
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        simp only [beq_iff_eq] at *
        obtain ⟨-, -, hhdr, -⟩ := h
        exact ⟨fun _ => by omega, fun _ => by omega, fun _ => by omega⟩
      · exact nomatch h

open Zstd.Native in
/-- `parseCompressedLiteralsHeader` returns the correct `fourStreams` value:
    `sizeFormat = 0 → false`, `sizeFormat ≥ 1 → true`. -/
theorem parseCompressedLiteralsHeader_fourStreams (data : ByteArray) (pos : Nat)
    (sizeFormat : Nat) (regen comp headerSize : Nat) (fourStreams : Bool)
    (h : parseCompressedLiteralsHeader data pos sizeFormat
         = .ok (regen, comp, headerSize, fourStreams)) :
    (sizeFormat = 0 → fourStreams = false) ∧
    (sizeFormat ≥ 1 → fourStreams = true) := by
  simp only [parseCompressedLiteralsHeader, pure, Except.pure] at h
  split at h
  · split at h
    · rename_i hsf _
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, -, hfs⟩ := h
      -- hfs : (sizeFormat == 1) = fourStreams
      constructor
      · intro heq; subst heq; exact hfs.symm
      · intro hge
        simp only [show sizeFormat = 1 from by omega, beq_self_eq_true] at hfs
        exact hfs.symm
    · exact nomatch h
  · split at h
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, -, hfs⟩ := h
        exact ⟨fun _ => by omega, fun _ => hfs.symm⟩
      · exact nomatch h
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨-, -, -, hfs⟩ := h
        exact ⟨fun _ => by omega, fun _ => hfs.symm⟩
      · exact nomatch h

open Zstd.Native in
/-- `parseCompressedLiteralsHeader` always returns `regen ≤ 0x3FFFF`.
    In all branches, `regen` is computed as `(raw >>> shift) &&& mask` where
    `mask ∈ {0x3FF, 0x3FFF, 0x3FFFF}`, and `x &&& mask ≤ mask ≤ 0x3FFFF`. -/
theorem parseCompressedLiteralsHeader_regen_bound (data : ByteArray) (pos : Nat)
    (sizeFormat : Nat) (regen comp headerSize : Nat) (fourStreams : Bool)
    (h : parseCompressedLiteralsHeader data pos sizeFormat
         = .ok (regen, comp, headerSize, fourStreams)) :
    regen ≤ 0x3FFFF := by
  simp only [parseCompressedLiteralsHeader, pure, Except.pure] at h
  split at h
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact Nat.le_trans Nat.and_le_right (by omega)
    · exact nomatch h
  · split at h
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1]; exact Nat.le_trans Nat.and_le_right (by omega)
      · exact nomatch h
    · split at h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.1]; exact Nat.and_le_right
      · exact nomatch h

/-! ## parseLiteralsSection structural properties (raw/RLE) -/

open Zstd.Native in
/-- For raw or RLE literals (types 0-1), the returned position is strictly
    greater than the input position, and the returned Huffman table is `none`. -/
private theorem parseLiteralsSection_simple_spec (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (hlit : (data[pos]! &&& 3).toNat ≤ 1)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    pos' > pos ∧ huffTable = none ∧ pos' ≤ data.size := by
  simp only [parseLiteralsSection, bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · split at h
    · exact nomatch h
    · split at h
      · rename_i hle3 hcomp
        simp only [beq_iff_eq, Bool.or_eq_true] at hcomp
        have : (data[pos]! &&& 3).toNat = 2 ∨ (data[pos]! &&& 3).toNat = 3 := hcomp
        omega
      · split at h
        · split at h
          · split at h
            · exact nomatch h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              exact ⟨by omega, h.2.2.symm, by omega⟩
          · split at h
            · exact nomatch h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              exact ⟨by omega, h.2.2.symm, by omega⟩
        · split at h
          · split at h
            · exact nomatch h
            · split at h
              · split at h
                · exact nomatch h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  exact ⟨by omega, h.2.2.symm, by omega⟩
              · split at h
                · exact nomatch h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  exact ⟨by omega, h.2.2.symm, by omega⟩
          · split at h
            · exact nomatch h
            · split at h
              · split at h
                · exact nomatch h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  exact ⟨by omega, h.2.2.symm, by omega⟩
              · split at h
                · exact nomatch h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  exact ⟨by omega, h.2.2.symm, by omega⟩

open Zstd.Native in
/-- For raw or RLE literals (types 0-1), the returned position advances. -/
theorem parseLiteralsSection_pos_gt_simple (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (hlit : (data[pos]! &&& 3).toNat ≤ 1)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    pos' > pos :=
  (parseLiteralsSection_simple_spec data pos prevHuffTree literals pos' huffTable hlit h).1

open Zstd.Native in
/-- For raw or RLE literals (types 0-1), no Huffman table is returned. -/
theorem parseLiteralsSection_huffTable_none_simple (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (hlit : (data[pos]! &&& 3).toNat ≤ 1)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    huffTable = none :=
  (parseLiteralsSection_simple_spec data pos prevHuffTree literals pos' huffTable hlit h).2.1

open Zstd.Native in
/-- For raw or RLE literals (types 0-1), the returned position stays within `data.size`. -/
theorem parseLiteralsSection_le_size_simple (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (hlit : (data[pos]! &&& 3).toNat ≤ 1)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    pos' ≤ data.size :=
  (parseLiteralsSection_simple_spec data pos prevHuffTree literals pos' huffTable hlit h).2.2

open Zstd.Native in
/-- Combined structural properties for compressed/treeless literals (types 2-3):
    the returned position advances and stays within `data.size`. -/
private theorem parseLiteralsSection_compressed_spec (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (hlit : (data[pos]! &&& 3).toNat ≥ 2)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    pos' > pos ∧ pos' ≤ data.size := by
  simp only [parseLiteralsSection, bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · split at h
    · exact nomatch h
    · split at h
      · split at h
        · exact nomatch h
        · rename_i v heq
          obtain ⟨regen, comp, hdr, fs⟩ := v
          have hge := parseCompressedLiteralsHeader_headerBytes_ge data pos _ _ _ _ _ heq
          split at h
          · split at h
            · split at h
              · exact nomatch h
              · split at h
                · exact nomatch h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact ⟨by omega, by omega⟩
            · exact nomatch h
          · split at h
            · exact nomatch h
            · split at h
              · exact nomatch h
              · split at h
                · exact nomatch h
                · split at h
                  · exact nomatch h
                  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact ⟨by omega, by omega⟩
      · rename_i hle3 hnotcomp
        simp only [beq_iff_eq, Bool.or_eq_true, not_or] at hnotcomp
        omega

open Zstd.Native in
/-- For compressed or treeless literals (types 2-3), the returned position advances. -/
theorem parseLiteralsSection_pos_gt_compressed (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (hlit : (data[pos]! &&& 3).toNat ≥ 2)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    pos' > pos :=
  (parseLiteralsSection_compressed_spec data pos prevHuffTree literals pos' huffTable hlit h).1

open Zstd.Native in
/-- For all literal types (0-3), the returned position advances. -/
theorem parseLiteralsSection_pos_gt (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    pos' > pos := by
  by_cases hlit : (data[pos]! &&& 3).toNat ≤ 1
  · exact parseLiteralsSection_pos_gt_simple data pos prevHuffTree literals pos' huffTable hlit h
  · exact parseLiteralsSection_pos_gt_compressed data pos prevHuffTree literals pos' huffTable
      (by omega) h

/-! ## parseLiteralsSection le_size properties -/

open Zstd.Native in
/-- For compressed or treeless literals (types 2-3), the returned position stays within
    `data.size`. The bounds check `data.size < afterHeader + compSize → throw` ensures
    `pos' = afterHeader + compSize ≤ data.size` on success. -/
theorem parseLiteralsSection_le_size_compressed (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (hlit : (data[pos]! &&& 3).toNat ≥ 2)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    pos' ≤ data.size :=
  (parseLiteralsSection_compressed_spec data pos prevHuffTree literals pos' huffTable hlit h).2

open Zstd.Native in
/-- For all literal types (0-3), the returned position stays within `data.size`. -/
theorem parseLiteralsSection_le_size (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    pos' ≤ data.size := by
  by_cases hlit : (data[pos]! &&& 3).toNat ≤ 1
  · exact parseLiteralsSection_le_size_simple data pos prevHuffTree literals pos' huffTable hlit h
  · exact parseLiteralsSection_le_size_compressed data pos prevHuffTree literals pos' huffTable
      (by omega) h

/-! ## parseLiteralsSection content properties -/

open Zstd.Native in
/-- For raw literals (type 0), the output is an exact contiguous slice of the input data:
    the bytes between the end of the variable-width header and `pos'`. -/
theorem parseLiteralsSection_raw_eq_extract (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (hlit : (data[pos]! &&& 3).toNat = 0)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable)) :
    ∃ afterHeader, afterHeader > pos ∧ afterHeader ≤ pos' ∧
      literals = data.extract afterHeader pos' := by
  simp only [parseLiteralsSection, bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · split at h
    · exact nomatch h
    · split at h
      · rename_i _ hcomp
        simp only [beq_iff_eq, Bool.or_eq_true] at hcomp
        have : (data[pos]! &&& 3).toNat = 2 ∨ (data[pos]! &&& 3).toNat = 3 := hcomp
        omega
      · split at h
        · split at h
          · split at h
            · exact nomatch h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, _⟩ := h
              exact ⟨pos + 1, by omega, by omega, rfl⟩
          · rename_i hne
            simp only [beq_iff_eq] at hne
            omega
        · split at h
          · split at h
            · exact nomatch h
            · split at h
              · split at h
                · exact nomatch h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl, _⟩ := h
                  exact ⟨pos + 2, by omega, by omega, rfl⟩
              · rename_i hne
                simp only [beq_iff_eq] at hne
                omega
          · split at h
            · exact nomatch h
            · split at h
              · split at h
                · exact nomatch h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl, _⟩ := h
                  exact ⟨pos + 3, by omega, by omega, rfl⟩
              · rename_i hne
                simp only [beq_iff_eq] at hne
                omega

open Zstd.Native in
/-- For RLE literals (type 1), all output bytes are identical: the mathematical
    essence of run-length encoding. -/
theorem parseLiteralsSection_rle_all_eq (data : ByteArray) (pos : Nat)
    (prevHuffTree : Option ZstdHuffmanTable)
    (literals : ByteArray) (pos' : Nat) (huffTable : Option ZstdHuffmanTable)
    (hlit : (data[pos]! &&& 3).toNat = 1)
    (h : parseLiteralsSection data pos prevHuffTree = .ok (literals, pos', huffTable))
    (i j : Nat) (hi : i < literals.size) (hj : j < literals.size) :
    literals[i] = literals[j] := by
  simp only [parseLiteralsSection, bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · split at h
    · exact nomatch h
    · split at h
      · rename_i _ hcomp
        simp only [beq_iff_eq, Bool.or_eq_true] at hcomp
        have : (data[pos]! &&& 3).toNat = 2 ∨ (data[pos]! &&& 3).toNat = 3 := hcomp
        omega
      · split at h
        · split at h
          · rename_i hne
            simp only [beq_iff_eq] at hne
            omega
          · split at h
            · exact nomatch h
            · simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, _, _⟩ := h
              rw [ByteArray.getElem_eq_getElem_data, Array.getElem_replicate,
                  ByteArray.getElem_eq_getElem_data, Array.getElem_replicate]
        · split at h
          · split at h
            · exact nomatch h
            · split at h
              · rename_i hne
                simp only [beq_iff_eq] at hne
                omega
              · split at h
                · exact nomatch h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, _, _⟩ := h
                  rw [ByteArray.getElem_eq_getElem_data, Array.getElem_replicate,
                      ByteArray.getElem_eq_getElem_data, Array.getElem_replicate]
          · split at h
            · exact nomatch h
            · split at h
              · rename_i hne
                simp only [beq_iff_eq] at hne
                omega
              · split at h
                · exact nomatch h
                · simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, _, _⟩ := h
                  rw [ByteArray.getElem_eq_getElem_data, Array.getElem_replicate,
                      ByteArray.getElem_eq_getElem_data, Array.getElem_replicate]

end Zstd.Spec.Huffman
