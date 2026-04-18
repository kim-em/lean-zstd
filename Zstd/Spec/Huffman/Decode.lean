import Zstd.Native.Huffman
import Zstd.Spec.Fse
import Zstd.Spec.Huffman.Table

/-!
# Properties of Huffman symbol / stream decoding

Monotonicity, size, and invariance properties for `decodeHuffmanSymbol`,
`decodeHuffmanStreamWF`, `decodeFourHuffmanStreamsWF`, plus the top-level
completeness lemmas for `decodeHuffmanLiterals` in both the single-stream
and four-stream modes. These rely on the `BackwardBitReader` `readBits`
lemmas from `Zstd.Spec.Fse`.
-/

namespace Zstd.Spec.Huffman

open Zstd.Native (ZstdHuffmanTable)

/-! ## decodeHuffmanSymbol properties -/

open Zstd.Native in
/-- Decompose a successful `decodeHuffmanSymbol` call: the result reader `br'`
    comes from a single `readBits` call on the original reader `br`.  This
    factors out the shared monadic unfolding used by `totalBitsRemaining_le`,
    `data_eq`, and `startPos_eq`. -/
private theorem decodeHuffmanSymbol_readBits_elim
    (htable : ZstdHuffmanTable) (br : BackwardBitReader)
    (sym : UInt8) (br' : BackwardBitReader)
    (h : decodeHuffmanSymbol htable br = .ok (sym, br')) :
    ∃ (bits : UInt32) (numBits : Nat),
      br.readBits numBits = .ok (bits, br') := by
  simp only [decodeHuffmanSymbol, bind, Except.bind] at h
  split at h; · exact nomatch h
  cases hrd1 : br.readBits (min htable.maxBits br.totalBitsRemaining) with
  | error => simp only [hrd1] at h; exact nomatch h
  | ok v1 =>
    obtain ⟨bits1, br1⟩ := v1
    rw [hrd1] at h
    dsimp only [pure, Pure.pure, Except.pure, Bind.bind, Except.bind] at h
    split at h
    · -- lookupVal < table.size
      split at h; · exact nomatch h  -- numBits > avail
      cases hrd2 : br.readBits _ with
      | error => rw [hrd2] at h; exact nomatch h
      | ok v2 =>
        obtain ⟨bits2, br2⟩ := v2
        rw [hrd2] at h
        dsimp only [] at h
        split at h
        · -- idx2 < table.size
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          exact ⟨_, _, hrd2⟩
        · exact nomatch h  -- idx2 ≥ table.size
    · exact nomatch h  -- lookupVal ≥ table.size

open Zstd.Native in
/-- When `decodeHuffmanSymbol` succeeds, the bit budget does not increase.
    This is the key monotonicity property for proving termination of
    Huffman stream decoding. -/
theorem decodeHuffmanSymbol_totalBitsRemaining_le
    (htable : ZstdHuffmanTable) (br : BackwardBitReader)
    (sym : UInt8) (br' : BackwardBitReader)
    (h : decodeHuffmanSymbol htable br = .ok (sym, br')) :
    br'.totalBitsRemaining ≤ br.totalBitsRemaining := by
  obtain ⟨_, _, hrd⟩ := decodeHuffmanSymbol_readBits_elim htable br sym br' h
  have := Zstd.Spec.Fse.readBits_totalBitsRemaining_sub br _ _ _ hrd
  omega

open Zstd.Native in
/-- The number of bits consumed is at most `maxBits`, given the table is
    well-formed (all entries have `numBits ≤ maxBits`). This bounds per-symbol
    cost and is needed for proving that stream decoding terminates within
    the available bit budget. -/
theorem decodeHuffmanSymbol_bits_le_maxBits
    (htable : ZstdHuffmanTable) (br : BackwardBitReader)
    (sym : UInt8) (br' : BackwardBitReader)
    (hvalid : ValidHuffmanTable htable.table htable.maxBits)
    (h : decodeHuffmanSymbol htable br = .ok (sym, br')) :
    br.totalBitsRemaining - br'.totalBitsRemaining ≤ htable.maxBits := by
  simp only [decodeHuffmanSymbol, bind, Except.bind] at h
  split at h; · exact nomatch h
  cases hrd1 : br.readBits (min htable.maxBits br.totalBitsRemaining) with
  | error => simp only [hrd1] at h; exact nomatch h
  | ok v1 =>
    obtain ⟨bits1, br1⟩ := v1
    rw [hrd1] at h
    dsimp only [pure, Pure.pure, Except.pure, Bind.bind, Except.bind] at h
    split at h
    · -- lookupVal < table.size
      rename_i hidx1
      split at h; · exact nomatch h  -- numBits > avail
      cases hrd2 : br.readBits _ with
      | error => rw [hrd2] at h; exact nomatch h
      | ok v2 =>
        obtain ⟨bits2, br2⟩ := v2
        rw [hrd2] at h
        dsimp only [] at h
        split at h
        · -- idx2 < table.size
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          have hsub := Zstd.Spec.Fse.readBits_totalBitsRemaining_sub br _ _ _ hrd2
          rw [hsub]
          -- numBits ≤ maxBits from ValidHuffmanTable and proven bounds
          -- readBits gives us br'.totalBitsRemaining = br.totalBitsRemaining - numBits
          -- where numBits = entry.numBits.toNat from the table lookup
          -- hvalid gives us entry.numBits.toNat ≤ maxBits
          -- The Fin vs Nat index discrepancy needs `show` to align
          suffices htable.table[bits1.toNat <<< (htable.maxBits -
            min htable.maxBits br.totalBitsRemaining)].numBits.toNat ≤ htable.maxBits by omega
          exact hvalid.2.1 ⟨_, hidx1⟩
        · exact nomatch h  -- idx2 ≥ table.size
    · exact nomatch h  -- lookupVal ≥ table.size

open Zstd.Native in
/-- The `data` field is unchanged by `decodeHuffmanSymbol`. -/
theorem decodeHuffmanSymbol_data_eq
    (htable : ZstdHuffmanTable) (br : BackwardBitReader)
    (sym : UInt8) (br' : BackwardBitReader)
    (h : decodeHuffmanSymbol htable br = .ok (sym, br')) :
    br'.data = br.data := by
  obtain ⟨_, _, hrd⟩ := decodeHuffmanSymbol_readBits_elim htable br sym br' h
  exact Zstd.Spec.Fse.readBits_data_eq br _ _ _ hrd

open Zstd.Native in
/-- The `startPos` field is unchanged by `decodeHuffmanSymbol`. -/
theorem decodeHuffmanSymbol_startPos_eq
    (htable : ZstdHuffmanTable) (br : BackwardBitReader)
    (sym : UInt8) (br' : BackwardBitReader)
    (h : decodeHuffmanSymbol htable br = .ok (sym, br')) :
    br'.startPos = br.startPos := by
  obtain ⟨_, _, hrd⟩ := decodeHuffmanSymbol_readBits_elim htable br sym br' h
  exact Zstd.Spec.Fse.readBits_startPos_eq br _ _ _ hrd

open Zstd.Native in
/-- If decoding succeeds, the input reader had bits remaining. This is the
    contrapositive of the `peekBits == 0` error check. -/
theorem decodeHuffmanSymbol_totalBitsRemaining_pos
    (htable : ZstdHuffmanTable) (br : BackwardBitReader)
    (sym : UInt8) (br' : BackwardBitReader)
    (h : decodeHuffmanSymbol htable br = .ok (sym, br')) :
    br.totalBitsRemaining > 0 := by
  simp only [decodeHuffmanSymbol, bind, Except.bind] at h
  split at h
  · exact nomatch h
  · rename_i hpb
    simp only [beq_iff_eq] at hpb
    omega

open Zstd.Native in
/-- When `decodeHuffmanStreamWF` succeeds, the output ByteArray has exactly
    `acc.size + count` bytes. -/
theorem decodeHuffmanStreamWF_size
    {htable : ZstdHuffmanTable} {br br' : BackwardBitReader}
    {count : Nat} {acc result : ByteArray}
    (h : decodeHuffmanStreamWF htable br count acc = .ok (result, br')) :
    result.size = acc.size + count := by
  induction count generalizing br acc with
  | zero =>
    simp only [decodeHuffmanStreamWF, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    omega
  | succ n ih =>
    simp only [decodeHuffmanStreamWF, bind, Except.bind] at h
    cases hsym : decodeHuffmanSymbol htable br with
    | error => simp only [hsym] at h; exact nomatch h
    | ok v =>
      obtain ⟨sym, br₁⟩ := v
      rw [hsym] at h; dsimp only [Bind.bind, Except.bind] at h
      have := ih h
      simp only [ByteArray.size_push] at this
      omega

open Zstd.Native in
/-- The bit budget is monotonically non-increasing through Huffman stream
    decoding: the final reader's `totalBitsRemaining` is at most the initial
    reader's. -/
theorem decodeHuffmanStreamWF_totalBitsRemaining_le
    {htable : ZstdHuffmanTable} {br br' : BackwardBitReader}
    {count : Nat} {acc result : ByteArray}
    (h : decodeHuffmanStreamWF htable br count acc = .ok (result, br')) :
    br'.totalBitsRemaining ≤ br.totalBitsRemaining := by
  induction count generalizing br acc with
  | zero =>
    simp only [decodeHuffmanStreamWF, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h; omega
  | succ n ih =>
    simp only [decodeHuffmanStreamWF, bind, Except.bind] at h
    cases hsym : decodeHuffmanSymbol htable br with
    | error => simp only [hsym] at h; exact nomatch h
    | ok v =>
      obtain ⟨sym, br₁⟩ := v
      rw [hsym] at h; dsimp only [Bind.bind, Except.bind] at h
      have h_step := decodeHuffmanSymbol_totalBitsRemaining_le htable br sym br₁ hsym
      have h_rec := ih h
      omega

open Zstd.Native in
/-- When `decodeFourHuffmanStreamsWF` succeeds, the output has exactly `regenSize`
    bytes.  The precondition `3 * ((regenSize + 3) / 4) ≤ regenSize` is needed
    because `perStream = (regenSize + 3) / 4` and the first three streams each
    decode `perStream` symbols; without this bound the Nat subtraction
    `regenSize - 3 * perStream` underflows, producing more than `regenSize`
    bytes.  The condition holds for all `regenSize ∉ {1, 2, 5}`, and in
    practice Zstd 4-stream mode requires `regenSize ≥ 256`. -/
theorem decodeFourHuffmanStreamsWF_size
    {htable : ZstdHuffmanTable} {data : ByteArray}
    {streamStart streamDataSize regenSize : Nat} {result : ByteArray}
    (h : decodeFourHuffmanStreamsWF htable data streamStart streamDataSize
           regenSize = .ok result)
    (hsize : 3 * ((regenSize + 3) / 4) ≤ regenSize) :
    result.size = regenSize := by
  simp only [decodeFourHuffmanStreamsWF, Bind.bind, Except.bind,
    Pure.pure, Except.pure] at h
  -- Eliminate 3 guard branches and 8 bind error branches
  iterate 11 (all_goals (try (first | contradiction | (split at h))))
  all_goals first
    | contradiction
    | (rename_i _ _ _ _ _ _ _ r1 hd1 _ _ _ _ r2 hd2 _ _ _ _ r3 hd3 _ _ _ _ r4 hd4
       simp only [Except.ok.injEq] at h; subst h
       simp only [ByteArray.size_append]
       have h1 := decodeHuffmanStreamWF_size hd1
       have h2 := decodeHuffmanStreamWF_size hd2
       have h3 := decodeHuffmanStreamWF_size hd3
       have h4 := decodeHuffmanStreamWF_size hd4
       simp only [ByteArray.size_empty] at h1 h2 h3 h4
       omega)

/-! ## decodeHuffmanLiterals completeness -/

open Zstd.Native in
/-- When `fourStreams = false`, `BackwardBitReader.init` succeeds, and
    `decodeHuffmanStream` succeeds, then `decodeHuffmanLiterals` succeeds. -/
theorem decodeHuffmanLiterals_succeeds_single
    (huffTable : ZstdHuffmanTable) (data : ByteArray)
    (streamStart streamDataSize regenSize : Nat)
    (br : BackwardBitReader)
    (hinit : BackwardBitReader.init data streamStart (streamStart + streamDataSize) = .ok br)
    (result : ByteArray)
    (hdecode : decodeHuffmanStream huffTable br regenSize = .ok result) :
    decodeHuffmanLiterals huffTable data streamStart streamDataSize regenSize false =
      .ok result := by
  simp only [decodeHuffmanLiterals, Bool.false_eq_true, ↓reduceIte, bind, Except.bind, hinit, hdecode]

open Zstd.Native in
/-- When `fourStreams = true` and `decodeFourHuffmanStreams` succeeds,
    then `decodeHuffmanLiterals` succeeds. -/
theorem decodeHuffmanLiterals_succeeds_four
    (huffTable : ZstdHuffmanTable) (data : ByteArray)
    (streamStart streamDataSize regenSize : Nat)
    (result : ByteArray)
    (hfour : decodeFourHuffmanStreams huffTable data streamStart streamDataSize regenSize = .ok result) :
    decodeHuffmanLiterals huffTable data streamStart streamDataSize regenSize true =
      .ok result := by
  simp only [decodeHuffmanLiterals, ite_true, hfour]

end Zstd.Spec.Huffman
