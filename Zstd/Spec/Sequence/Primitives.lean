import Zstd.Native.Sequence
import ZipForStd.ByteArray

/-!
# Size and content lemmas for sequence execution primitives

Low-level building blocks for reasoning about Zstd sequence execution:
`copyBytes` and `copyMatch` size/content characterizations, plus the loop
invariants for `executeSequences.loop` that follow from them.
-/

namespace Zstd.Native

/-! ## Size lemmas for sequence execution helpers -/

/-- `copyBytes` increases destination size by exactly `count`. -/
theorem copyBytes_size (dst : ByteArray) (src : ByteArray) (srcPos count : Nat) :
    (copyBytes dst src srcPos count).size = dst.size + count := by
  induction count generalizing dst srcPos with
  | zero => simp only [copyBytes, ↓reduceIte]; omega
  | succ n ih =>
    rw [copyBytes.eq_1]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [ih, ByteArray.size_push]; omega

/-- `copyBytes` preserves existing destination bytes: for `i < dst.size`,
    `(copyBytes dst src srcPos count)[i]! = dst[i]!`. -/
theorem copyBytes_getElem_lt (dst src : ByteArray) (srcPos count : Nat) (i : Nat)
    (hi : i < dst.size) :
    (copyBytes dst src srcPos count)[i]! = dst[i]! := by
  induction count generalizing dst srcPos with
  | zero => simp only [copyBytes, ↓reduceIte]
  | succ n ih =>
    rw [copyBytes.eq_1]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [ih (dst.push src[srcPos]!) (srcPos + 1) (by simp only [ByteArray.size_push]; omega)]
    exact ByteArray.push_getElem!_lt dst src[srcPos]! i hi

/-- `copyBytes` content at new positions: the j-th new byte equals `src[srcPos + j]!`.
    For `j < count` with `srcPos + j < src.size`,
    `(copyBytes dst src srcPos count)[dst.size + j]! = src[srcPos + j]!`. -/
theorem copyBytes_getElem_ge (dst src : ByteArray) (srcPos count : Nat) (j : Nat)
    (hj : j < count) (hsrc : srcPos + count ≤ src.size) :
    (copyBytes dst src srcPos count)[dst.size + j]! = src[srcPos + j]! := by
  induction count generalizing dst srcPos j with
  | zero => omega
  | succ n ih =>
    rw [copyBytes.eq_1]
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    cases j with
    | zero =>
      -- The first new byte: after pushing src[srcPos]!, it's at dst.size
      simp only [Nat.add_zero]
      rw [copyBytes_getElem_lt _ _ _ _ dst.size (by simp only [ByteArray.size_push]; omega)]
      exact ByteArray.push_getElem!_eq dst src[srcPos]!
    | succ j' =>
      -- Later new bytes: use the IH on the recursive call
      have : dst.size + (j' + 1) = (dst.push src[srcPos]!).size + j' := by
        simp only [ByteArray.size_push]; omega
      rw [this, ih (dst.push src[srcPos]!) (srcPos + 1) j' (by omega) (by omega)]
      congr 1; omega

private theorem copyMatch_loop_size (offset length start : Nat) (b : ByteArray) (k : Nat)
    (hk : k ≤ length) :
    (copyMatch.loop offset length start b k).size = b.size + (length - k) := by
  rw [copyMatch.loop.eq_1]
  split
  · rename_i hlt
    rw [copyMatch_loop_size offset length start _ (k + 1) (by omega), ByteArray.size_push]; omega
  · rename_i hge; omega
  termination_by length - k

/-- `copyMatch` increases buffer size by exactly `length`. -/
theorem copyMatch_size (buf : ByteArray) (offset length : Nat) :
    (copyMatch buf offset length).size = buf.size + length := by
  unfold copyMatch
  exact copyMatch_loop_size offset length (buf.size - offset) buf 0 (Nat.zero_le _)

private theorem copyMatch_loop_getElem_lt (offset length start : Nat) (b : ByteArray)
    (k : Nat) (_hk : k ≤ length) (i : Nat) (hi : i < b.size) :
    (copyMatch.loop offset length start b k)[i]! = b[i]! := by
  rw [copyMatch.loop.eq_1]
  split
  · rename_i hlt
    rw [copyMatch_loop_getElem_lt offset length start _ (k + 1) (by omega) i
      (by simp only [ByteArray.size_push]; omega)]
    exact ByteArray.push_getElem!_lt b _ i hi
  · rfl
  termination_by length - k

/-- `copyMatch` preserves existing buffer bytes: for `i < buf.size`,
    `(copyMatch buf offset length)[i]! = buf[i]!`. -/
theorem copyMatch_getElem_lt (buf : ByteArray) (offset length : Nat) (i : Nat)
    (hi : i < buf.size) :
    (copyMatch buf offset length)[i]! = buf[i]! := by
  unfold copyMatch
  exact copyMatch_loop_getElem_lt offset length (buf.size - offset) buf 0 (Nat.zero_le _) i hi

private theorem copyMatch_loop_getElem_ge_nonoverlap (offset length start : Nat)
    (buf b : ByteArray) (k j : Nat)
    (hoff : offset ≥ length)
    (hstart : start = buf.size - offset)
    (hreach : offset ≤ buf.size)
    (hbsize : b.size = buf.size + k)
    (hprefix : ∀ i, i < buf.size → b[i]! = buf[i]!)
    (hk : k ≤ length)
    (hj : j < length - k) :
    (copyMatch.loop offset length start b k)[b.size + j]! = buf[start + (k + j)]! := by
  rw [copyMatch.loop.eq_1]
  have hklt : k < length := by omega
  simp only [hklt, ↓reduceIte]
  have hkmod : k % offset = k := Nat.mod_eq_of_lt (by omega)
  have hsk : start + k < buf.size := by omega
  rw [hkmod]
  cases j with
  | zero =>
    simp only [Nat.add_zero]
    rw [copyMatch_loop_getElem_lt offset length start _ (k + 1) (by omega)
      b.size (by simp only [ByteArray.size_push]; omega)]
    rw [ByteArray.push_getElem!_eq]
    exact hprefix _ hsk
  | succ j' =>
    have heq : b.size + (j' + 1) = (b.push b[start + k]!).size + j' := by
      simp only [ByteArray.size_push]; omega
    rw [heq, copyMatch_loop_getElem_ge_nonoverlap offset length start buf _ (k + 1) j'
      hoff hstart hreach (by simp only [ByteArray.size_push, hbsize]; omega)
      (fun i hi => by rw [ByteArray.push_getElem!_lt _ _ _ (by omega)]; exact hprefix i hi)
      (by omega) (by omega)]
    congr 1; omega
  termination_by length - k

/-- `copyMatch` content at new positions (non-overlapping case): when `offset ≥ length`,
    the j-th new byte equals the byte `offset` positions back in the original buffer.
    For `j < length`, `(copyMatch buf offset length)[buf.size + j]! = buf[buf.size - offset + j]!`.
    Combined with `copyMatch_getElem_lt` and `copyMatch_size`, this fully specifies `copyMatch`
    when the source region doesn't overlap the destination. -/
theorem copyMatch_getElem_ge_nonoverlap (buf : ByteArray) (offset length : Nat) (j : Nat)
    (hoff : offset ≥ length) (hreach : offset ≤ buf.size) (hj : j < length) :
    (copyMatch buf offset length)[buf.size + j]! = buf[buf.size - offset + j]! := by
  unfold copyMatch
  simp only
  have := copyMatch_loop_getElem_ge_nonoverlap offset length (buf.size - offset) buf buf 0 j
    hoff rfl hreach rfl (fun _ _ => rfl) (Nat.zero_le _) (by omega)
  simp only [Nat.zero_add] at this
  exact this

private theorem copyMatch_loop_getElem_ge (offset length start : Nat)
    (buf b : ByteArray) (k j : Nat)
    (hoff : offset > 0) (hstart : start + offset = buf.size)
    (hbsize : b.size = buf.size + k)
    (hprefix : ∀ i, i < buf.size → b[i]! = buf[i]!)
    (hk : k ≤ length)
    (hj : j < length - k) :
    (copyMatch.loop offset length start b k)[b.size + j]! =
      buf[start + ((k + j) % offset)]! := by
  rw [copyMatch.loop.eq_1]
  have hklt : k < length := by omega
  simp only [hklt, ↓reduceIte]
  have hsk : start + (k % offset) < buf.size := by
    have := Nat.mod_lt k hoff; omega
  cases j with
  | zero =>
    simp only [Nat.add_zero]
    rw [copyMatch_loop_getElem_lt offset length start _ (k + 1) (by omega)
      b.size (by simp only [ByteArray.size_push]; omega)]
    rw [ByteArray.push_getElem!_eq]
    exact hprefix _ hsk
  | succ j' =>
    have heq : b.size + (j' + 1) = (b.push b[start + (k % offset)]!).size + j' := by
      simp only [ByteArray.size_push]; omega
    simp only [show k + (j' + 1) = k + 1 + j' from by omega]
    rw [heq, copyMatch_loop_getElem_ge offset length start buf _ (k + 1) j'
      hoff hstart (by simp only [ByteArray.size_push, hbsize]; omega)
      (fun i hi => by rw [ByteArray.push_getElem!_lt _ _ _ (by omega)]; exact hprefix i hi)
      (by omega) (by omega)]
  termination_by length - k

/-- `copyMatch` content at new positions (general case, including overlap): the j-th
    new byte equals the byte at position `buf.size - offset + (j % offset)` in the
    original buffer. This captures the cyclic repetition semantics of LZ77
    back-references (RFC 1951 §3.2.3, RFC 8878 §3.1.1.4).

    Combined with `copyMatch_getElem_lt` (preservation) and `copyMatch_size` (size),
    this fully specifies `copyMatch` for ALL cases — including overlapping matches
    used for run-length encoding and pattern repetition.

    Subsumes `copyMatch_getElem_ge_nonoverlap`: when `offset ≥ length`, `j < length`
    implies `j % offset = j` by `Nat.mod_eq_of_lt`. -/
theorem copyMatch_getElem_ge (buf : ByteArray) (offset length : Nat) (j : Nat)
    (hoff : offset > 0) (hreach : offset ≤ buf.size) (hj : j < length) :
    (copyMatch buf offset length)[buf.size + j]! =
      buf[buf.size - offset + (j % offset)]! := by
  unfold copyMatch
  simp only
  have := copyMatch_loop_getElem_ge offset length (buf.size - offset) buf buf 0 j
    hoff (by omega) rfl (fun _ _ => rfl) (Nat.zero_le _) (by omega)
  simp only [Nat.zero_add] at this
  exact this

protected theorem foldl_nat_add (f : ZstdSequence → Nat) (init : Nat) (seqs : List ZstdSequence) :
    List.foldl (fun acc s => acc + f s) init seqs =
    init + List.foldl (fun acc s => acc + f s) 0 seqs := by
  induction seqs generalizing init with
  | nil => simp only [List.foldl_nil, Nat.add_zero]
  | cons s rest ih =>
    simp only [List.foldl_cons]
    rw [ih, ih 0, ih (0 + f s)]
    omega

/-! ## executeSequences loop invariants -/

/-- Loop invariant: if `executeSequences.loop` succeeds, the output size equals
    initial output size + literals consumed + match bytes, litPos bounds hold,
    and the output is at least as large as the input (monotonicity). -/
theorem executeSequences_loop_inv (seqs : List ZstdSequence) (literals : ByteArray)
    (output : ByteArray) (history : Array Nat) (litPos : Nat) (windowSize : Nat)
    (output' : ByteArray) (history' : Array Nat) (litPos' : Nat)
    (hlp : litPos ≤ literals.size)
    (h : executeSequences.loop seqs literals output history litPos windowSize
         = .ok (output', history', litPos')) :
    output'.size = output.size + (litPos' - litPos) +
      List.foldl (fun acc (s : ZstdSequence) => acc + s.matchLength) 0 seqs
    ∧ litPos ≤ litPos'
    ∧ litPos' ≤ literals.size
    ∧ output'.size ≥ output.size := by
  induction seqs generalizing output history litPos with
  | nil =>
    rw [executeSequences.loop.eq_1] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _, rfl⟩ := h
    exact ⟨by simp only [List.foldl_nil]; omega, Nat.le_refl _, hlp, Nat.le_refl _⟩
  | cons seq rest ih =>
    rw [executeSequences.loop.eq_2] at h
    split at h; · exact nomatch h
    rename_i hlit
    split at h; dsimp only [letFun] at h
    split at h; · exact nomatch h
    split at h; · exact nomatch h
    split at h; · exact nomatch h
    have hlp' : litPos + seq.literalLength ≤ literals.size := by omega
    have ⟨ih_size, ih_le, ih_bound, ih_mono⟩ := ih _ _ _ hlp' h
    rw [copyMatch_size, copyBytes_size] at ih_size ih_mono
    refine ⟨?_, ?_, ih_bound, by omega⟩
    · rw [ih_size]
      simp only [List.foldl_cons, Nat.zero_add]
      conv => rhs; rw [Zstd.Native.foldl_nat_add]
      generalize List.foldl (fun acc s => acc + s.matchLength) 0 rest = matchSum
      omega
    · omega

/-- The `executeSequences.loop` output buffer is always at least as large as the
    input buffer. Corollary of `executeSequences_loop_inv`. -/
theorem executeSequences_loop_output_size_ge
    (seqs : List ZstdSequence) (literals : ByteArray)
    (output : ByteArray) (history : Array Nat) (litPos windowSize : Nat)
    (result : ByteArray × Array Nat × Nat)
    (h : executeSequences.loop seqs literals output history litPos windowSize
         = .ok result) :
    result.1.size ≥ output.size := by
  obtain ⟨output', history', litPos'⟩ := result
  show output'.size ≥ output.size
  cases seqs with
  | nil =>
    rw [executeSequences.loop.eq_1] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _, _⟩ := h; omega
  | cons seq rest =>
    have h' := h
    rw [executeSequences.loop.eq_2] at h'
    split at h'
    · exact nomatch h'
    · exact (executeSequences_loop_inv _ _ _ _ _ _ _ _ _ (by omega) h).2.2.2

/-- Single-step unfolding: when all guards pass, processing `seq :: rest` equals
    processing `rest` with the intermediate state after one copy-literal +
    resolve-offset + copy-match step. This is the fundamental building block
    for compositional reasoning about `executeSequences.loop`. -/
theorem executeSequences_loop_cons (seq : ZstdSequence) (rest : List ZstdSequence)
    (literals : ByteArray) (output : ByteArray) (history : Array Nat)
    (litPos windowSize : Nat)
    (hlit : litPos + seq.literalLength ≤ literals.size)
    (hoff : (resolveOffset seq.offset history seq.literalLength).1 ≠ 0)
    (hreach : (resolveOffset seq.offset history seq.literalLength).1
      ≤ (copyBytes output literals litPos seq.literalLength).size)
    (hwin : windowSize = 0
      ∨ (resolveOffset seq.offset history seq.literalLength).1 ≤ windowSize) :
    executeSequences.loop (seq :: rest) literals output history litPos windowSize =
      let output' := copyBytes output literals litPos seq.literalLength
      let (offset, history') := resolveOffset seq.offset history seq.literalLength
      let output'' := copyMatch output' offset seq.matchLength
      executeSequences.loop rest literals output'' history'
        (litPos + seq.literalLength) windowSize := by
  rw [executeSequences.loop.eq_2]
  simp only [show ¬(litPos + seq.literalLength > literals.size) from by omega, ↓reduceIte]
  split
  · rename_i h; exact absurd (beq_iff_eq.mp h) hoff
  · split
    · rename_i h; exact absurd hreach (by omega)
    · split
      · rename_i h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        exact absurd h.2 (by cases hwin with | inl hw => omega | inr hw => omega)
      · rfl

/-- After processing one sequence, the intermediate output has grown by exactly
    `seq.literalLength + seq.matchLength` bytes. Composes `copyMatch_size` and
    `copyBytes_size`. -/
theorem executeSequences_loop_cons_output_size (seq : ZstdSequence)
    (literals : ByteArray) (output : ByteArray) (history : Array Nat)
    (litPos : Nat) :
    let output' := copyBytes output literals litPos seq.literalLength
    let (offset, _) := resolveOffset seq.offset history seq.literalLength
    (copyMatch output' offset seq.matchLength).size =
      output.size + seq.literalLength + seq.matchLength := by
  simp only [copyMatch_size, copyBytes_size]

/-- When the sequence execution loop succeeds, every byte that was in the
    output buffer before the loop started is still there at the same index.
    This composes `copyBytes_getElem_lt` and `copyMatch_getElem_lt` through
    the recursive loop structure via induction on the sequence list. -/
theorem executeSequences_loop_getElem_lt
    (seqs : List ZstdSequence) (literals : ByteArray)
    (output : ByteArray) (history : Array Nat) (litPos : Nat) (windowSize : Nat)
    (result : ByteArray × Array Nat × Nat)
    (h : executeSequences.loop seqs literals output history litPos windowSize
         = .ok result)
    (i : Nat) (hi : i < output.size) :
    result.1[i]! = output[i]! := by
  induction seqs generalizing output history litPos with
  | nil =>
    rw [executeSequences.loop.eq_1] at h
    simp only [Except.ok.injEq] at h
    obtain ⟨rfl, _, _⟩ := h; rfl
  | cons seq rest ih =>
    rw [executeSequences.loop.eq_2] at h
    split at h; · exact nomatch h
    split at h; dsimp only [letFun] at h
    split at h; · exact nomatch h
    split at h; · exact nomatch h
    split at h; · exact nomatch h
    have hcb_size := copyBytes_size output literals litPos seq.literalLength
    have hi_cb : i < (copyBytes output literals litPos seq.literalLength).size := by
      rw [hcb_size]; omega
    exact ih _ _ _ h (by rw [copyMatch_size, hcb_size]; omega)
      |>.trans (copyMatch_getElem_lt _ _ _ _ hi_cb)
      |>.trans (copyBytes_getElem_lt _ _ _ _ _ hi)

end Zstd.Native
