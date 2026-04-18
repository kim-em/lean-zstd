import Zstd.Native.Sequence
import Zstd.Spec.Fse

/-!
# `resolveSingleFseTable` and `decodeSequencesWF` completeness

Per-mode succeeds lemmas for `resolveSingleFseTable`: predefined mode
is unconditional; RLE needs one byte; repeat needs a previous table;
fseCompressed needs a successful distribution+table build. Paired with
output-size characterizations for `decodeSequencesWF` (zero sequences
returns empty; a successful loop yields exactly the requested count).
-/

namespace Zstd.Native

open ZipCommon (BitReader)

/-! ## resolveSingleFseTable completeness -/

/-- In predefined mode, `resolveSingleFseTable` always succeeds (unconditionally).
    The only fallible operation is `buildFseTable`, which always succeeds by `buildFseTable_ok`. -/
theorem resolveSingleFseTable_succeeds_predefined (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable) :
    ∃ table,
      resolveSingleFseTable .predefined maxSymbols maxAccLog data pos
        predefinedDist predefinedAccLog prevTable = .ok (table, pos) := by
  simp only [resolveSingleFseTable, pure, Except.pure]
  obtain ⟨t, ht⟩ := Zstd.Spec.Fse.buildFseTable_ok predefinedDist predefinedAccLog
  rw [ht]
  exact ⟨t, rfl⟩

/-- In RLE mode, `resolveSingleFseTable` succeeds when there is at least 1 byte at `pos`. -/
theorem resolveSingleFseTable_succeeds_rle (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (hsize : data.size ≥ pos + 1) :
    ∃ table,
      resolveSingleFseTable .rle maxSymbols maxAccLog data pos
        predefinedDist predefinedAccLog prevTable = .ok (table, pos + 1) := by
  simp only [resolveSingleFseTable, pure, Except.pure]
  have : ¬(data.size < pos + 1) := by omega
  simp only [this, dite_false]
  exact ⟨_, rfl⟩

/-- In repeat mode, `resolveSingleFseTable` succeeds when a previous table is available. -/
theorem resolveSingleFseTable_succeeds_repeat (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (table : FseTable) :
    resolveSingleFseTable .repeat maxSymbols maxAccLog data pos
      predefinedDist predefinedAccLog (some table) = .ok (table, pos) := by
  simp only [resolveSingleFseTable, pure, Except.pure]

/-- In FSE-compressed mode, `resolveSingleFseTable` succeeds when
    `decodeFseDistribution` and `buildFseTable` both succeed. -/
theorem resolveSingleFseTable_succeeds_fse (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (probs : Array Int32) (accLog : Nat) (br' : BitReader)
    (hfse : decodeFseDistribution ⟨data, pos, 0⟩ maxSymbols maxAccLog
            = .ok (probs, accLog, br'))
    (table : FseTable)
    (hbuild : buildFseTable probs accLog = .ok table) :
    resolveSingleFseTable .fseCompressed maxSymbols maxAccLog data pos
      predefinedDist predefinedAccLog prevTable =
      .ok (table, if br'.bitOff == 0 then br'.pos else br'.pos + 1) := by
  simp only [resolveSingleFseTable, bind, Except.bind, hfse, hbuild, pure, Except.pure]

/-! ## decodeSequencesWF completeness -/

/-- When `numSeq = 0`, `decodeSequencesWF` returns an empty array and
    the unchanged backward bit reader. -/
theorem decodeSequencesWF_succeeds_zero
    (litLenTable offsetTable matchLenTable : FseTable)
    (br : BackwardBitReader) :
    decodeSequencesWF litLenTable offsetTable matchLenTable br 0 =
      .ok (#[], br) := by
  simp only [decodeSequencesWF, beq_self_eq_true, ↓reduceIte]

/-! ## decodeSequencesWF output size -/

/-- When the inner loop succeeds, the output array has exactly
    `acc.size + remaining` elements. -/
theorem decodeSequencesWF_loop_size
    {litLenTable offsetTable matchLenTable : FseTable}
    {br br' : BackwardBitReader}
    {litLenState offsetState matchLenState remaining total : Nat}
    {acc result : Array ZstdSequence}
    (h : decodeSequencesWF.loop litLenTable offsetTable matchLenTable br
           litLenState offsetState matchLenState remaining total acc
           = .ok (result, br')) :
    result.size = acc.size + remaining := by
  induction remaining generalizing br litLenState offsetState matchLenState acc with
  | zero =>
    simp only [decodeSequencesWF.loop, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h; omega
  | succ n ih =>
    simp only [decodeSequencesWF.loop] at h
    split at h; · exact nomatch h  -- bounds check 1
    split at h; · exact nomatch h  -- bounds check 2
    split at h; · exact nomatch h  -- bounds check 3
    split at h; · exact nomatch h  -- decodeOneSequence
    simp only [beq_iff_eq] at h
    split at h
    · -- Last sequence
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      simp only [Array.size_push]; omega
    · -- Not last: 3 readBits for state update + recursion
      split at h; · exact nomatch h
      split at h; · exact nomatch h
      split at h; · exact nomatch h
      rw [ih h]; simp only [Array.size_push]; omega

/-- When `decodeSequencesWF` succeeds with `numSeq > 0`, the result has
    exactly `numSeq` elements. -/
theorem decodeSequencesWF_size
    {litLenTable offsetTable matchLenTable : FseTable}
    {br br' : BackwardBitReader}
    {numSeq : Nat} {result : Array ZstdSequence}
    (h : decodeSequencesWF litLenTable offsetTable matchLenTable br numSeq
           = .ok (result, br'))
    (hcount : 0 < numSeq) :
    result.size = numSeq := by
  simp only [decodeSequencesWF] at h
  split at h
  · rename_i h0; simp only [beq_iff_eq] at h0; omega
  · split at h; · exact nomatch h
    split at h; · exact nomatch h
    split at h; · exact nomatch h
    have := decodeSequencesWF_loop_size h
    simp only [Array.size_empty] at this; omega

end Zstd.Native
