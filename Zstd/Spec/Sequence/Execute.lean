import Zstd.Spec.Sequence.Primitives
import Zstd.Spec.Sequence.Validity

/-!
# `executeSequences` output characterization and completeness

The wrapper-level theorems tying `executeSequences` to the
`ValidOffsetHistory` predicate and spelling out when it succeeds.
Includes:

* `executeSequences_output_length` / `executeSequences_empty`:
  output-size characterizations,
* history preservation lifts (`_history_valid`, `_history_size`),
* `OffsetsValidForLoop`: a recursive per-step offset-validity predicate
  tracking the threaded history,
* the completeness pair `executeSequences_loop_succeeds` /
  `executeSequences_succeeds`, proving `.ok` from sufficient preconditions.
-/

namespace Zstd.Spec.Sequence

open Zstd.Native (ZstdSequence resolveOffset executeSequences
  executeSequences_loop_inv copyBytes_size copyMatch_size)

/-- `executeSequences` output size characterization: when `executeSequences`
    succeeds with an empty window prefix, the output contains exactly the
    literal bytes consumed plus match bytes copied. -/
theorem executeSequences_output_length (seqs : Array ZstdSequence) (literals : ByteArray)
    (history : Array Nat) (output : ByteArray) (history' : Array Nat)
    (h : executeSequences seqs literals ByteArray.empty history = .ok (output, history')) :
    output.size = literals.size +
      seqs.foldl (fun acc s => acc + s.matchLength) 0 := by
  unfold executeSequences at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  split at h
  · exact nomatch h
  · rename_i v heq
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hout, _⟩ := h
    have ⟨hsize, _, hbound, _⟩ := executeSequences_loop_inv _ _ _ _ _ _ _ _ _ (Nat.zero_le _) heq
    rw [ByteArray.size_empty, Nat.zero_add, Nat.sub_zero] at hsize
    rw [← hout, ByteArray.size_extract, copyBytes_size, hsize]
    rw [← Array.foldl_toList]
    simp only [Nat.min_self, ByteArray.size_empty]
    omega

/-! ## Base case and monotonicity for executeSequences -/

/-- When the sequence array is empty, `executeSequences` succeeds with block
    output of size equal to `literals.size`, and the offset history is unchanged.
    This is the base case for inductive arguments about sequence execution;
    Zstd frames with only raw or RLE blocks have no sequences, so this theorem
    directly characterizes their sequence execution step. -/
theorem executeSequences_empty (literals : ByteArray)
    (windowPrefix : ByteArray) (history : Array Nat) (windowSize : Nat)
    (blockOutput : ByteArray) (history' : Array Nat)
    (h : executeSequences #[] literals windowPrefix history windowSize
         = .ok (blockOutput, history')) :
    blockOutput.size = literals.size ∧ history' = history := by
  unfold executeSequences at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure,
    Zstd.Native.executeSequences.loop, Nat.sub_zero] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hout, hhist⟩ := h
  exact ⟨by rw [← hout, ByteArray.size_extract, copyBytes_size]; omega, hhist.symm⟩

/-- When `executeSequences` succeeds and the input offset history is valid,
    the output offset history is also valid. Lifts `executeSequences_loop_history_valid`
    through the monadic wrapper. -/
theorem executeSequences_history_valid
    (sequences : Array ZstdSequence) (literals : ByteArray)
    (windowPrefix : ByteArray) (offsetHistory : Array Nat) (windowSize : Nat)
    (blockOutput : ByteArray) (history' : Array Nat)
    (hvalid : ValidOffsetHistory offsetHistory)
    (h : executeSequences sequences literals windowPrefix offsetHistory windowSize
         = .ok (blockOutput, history')) :
    ValidOffsetHistory history' := by
  unfold executeSequences at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  split at h
  · exact nomatch h
  · rename_i v heq
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact executeSequences_loop_history_valid _ _ _ _ _ _ _ _ _ hvalid heq

/-- The output history from `executeSequences` has exactly 3 entries when the
    input history does. Uses the weaker hypothesis `offsetHistory.size = 3`
    rather than full `ValidOffsetHistory`. -/
theorem executeSequences_history_size
    (sequences : Array ZstdSequence) (literals : ByteArray)
    (windowPrefix : ByteArray) (offsetHistory : Array Nat) (windowSize : Nat)
    (blockOutput : ByteArray) (history' : Array Nat)
    (hinit : offsetHistory.size = 3)
    (h : executeSequences sequences literals windowPrefix offsetHistory windowSize
         = .ok (blockOutput, history')) :
    history'.size = 3 := by
  unfold executeSequences at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  split at h
  · exact nomatch h
  · rename_i v heq
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact executeSequences_loop_history_size _ _ _ _ _ _ _ _ _ hinit heq

/-! ## Literal length foldl commutativity -/

private theorem foldl_litLen_add (init : Nat) (seqs : List ZstdSequence) :
    List.foldl (fun acc (s : ZstdSequence) => acc + s.literalLength) init seqs =
    init + List.foldl (fun acc (s : ZstdSequence) => acc + s.literalLength) 0 seqs :=
  Zstd.Native.foldl_nat_add _ init seqs

/-! ## executeSequences completeness

These theorems prove WHEN `executeSequences.loop` and `executeSequences` succeed,
complementing the existing invariant theorems which assume success. The key missing
link for composed completeness of compressed blocks with sequences. -/

/-- Recursive predicate capturing per-step offset validity for the sequence loop.
    At each step, the resolved offset must be positive (nonzero raw offset + shift-3
    safety) and within window bounds. The predicate threads the history state through
    each `resolveOffset` call, matching how the loop itself evolves the history. -/
def OffsetsValidForLoop : List ZstdSequence → Array Nat → Nat → Nat → Prop
  | [], _, _, _ => True
  | seq :: rest, history, litPos, windowSize =>
    seq.offset > 0
    ∧ (seq.literalLength = 0 ∧ seq.offset = 3 → history[0]! ≥ 2)
    ∧ (windowSize > 0 → (resolveOffset seq.offset history seq.literalLength).1 ≤ windowSize)
    ∧ OffsetsValidForLoop rest
        (resolveOffset seq.offset history seq.literalLength).2
        (litPos + seq.literalLength) windowSize

/-- `executeSequences.loop` succeeds when:
    (1) total literal consumption fits within the literals buffer,
    (2) offset validity holds at each step (positive, within window),
    (3) `windowSize > 0` (windowed mode — the common case for compressed blocks), and
    (4) the output buffer is at least as large as `windowSize` (so window-bounded
        offsets are within reach of the output buffer).

    This is the critical completeness theorem: existing theorems assume `.ok`,
    while this one PROVES `.ok` from sufficient conditions. The windowed-mode
    restriction (`windowSize > 0`) simplifies the offset-reach argument — all
    resolved offsets are ≤ windowSize ≤ output.size. -/
theorem executeSequences_loop_succeeds
    (seqs : List ZstdSequence) (literals : ByteArray)
    (output : ByteArray) (history : Array Nat) (litPos : Nat) (windowSize : Nat)
    (hlit : litPos + List.foldl (fun acc (s : ZstdSequence) => acc + s.literalLength) 0 seqs
            ≤ literals.size)
    (hvalid : ValidOffsetHistory history)
    (hoffsets : OffsetsValidForLoop seqs history litPos windowSize)
    (hws : windowSize > 0)
    (hout : output.size ≥ windowSize) :
    ∃ output' history' litPos',
      Zstd.Native.executeSequences.loop seqs literals output history litPos windowSize
        = .ok (output', history', litPos') := by
  induction seqs generalizing output history litPos with
  | nil =>
    exact ⟨output, history, litPos, rfl⟩
  | cons seq rest ih =>
    rw [Zstd.Native.executeSequences.loop.eq_2]
    -- Guard 1: enough literals
    have hlit1 : ¬(litPos + seq.literalLength > literals.size) := by
      simp only [List.foldl_cons, Nat.zero_add] at hlit
      rw [foldl_litLen_add] at hlit; omega
    simp only [hlit1, ↓reduceIte]
    -- Extract offset validity components
    obtain ⟨hraw_pos, hshift3, hwin_bound, hrest_valid⟩ := hoffsets
    -- Guard 2: offset ≠ 0
    have hoff_pos : (resolveOffset seq.offset history seq.literalLength).1 > 0 :=
      resolveOffset_positive_all seq.offset history seq.literalLength hraw_pos hvalid hshift3
    split
    · -- offset == 0: contradiction with positivity
      rename_i heq0; exact absurd (beq_iff_eq.mp heq0) (by omega)
    · -- Guard 3: offset ≤ output'.size
      have hcb_size := copyBytes_size output literals litPos seq.literalLength
      split
      · -- offset > output.size: contradiction (offset ≤ windowSize ≤ output.size)
        rename_i hreach; exact absurd hreach (by
          have := hwin_bound hws; rw [hcb_size]; omega)
      · -- Guard 4: window size bound
        split
        · -- windowSize > 0 && offset > windowSize: contradiction
          rename_i hwinv
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hwinv
          exact absurd hwinv.2 (Nat.not_lt.mpr (hwin_bound hws))
        · -- All guards passed, apply inductive hypothesis
          apply ih
          · -- hlit: literal consumption for rest
            simp only [List.foldl_cons, Nat.zero_add] at hlit
            rw [foldl_litLen_add] at hlit; omega
          · exact resolveOffset_history_valid_of_fst_ne_zero _ _ _ hvalid (by omega)
          · exact hrest_valid
          · rw [copyMatch_size, hcb_size]; omega

/-- Lifts `executeSequences_loop_succeeds` to the wrapper function.
    After the loop succeeds, `copyBytes` for remaining literals and
    `ByteArray.extract` for the block output are both total operations,
    so the lifting is mechanical. -/
theorem executeSequences_succeeds
    (sequences : Array ZstdSequence) (literals : ByteArray)
    (windowPrefix : ByteArray) (offsetHistory : Array Nat) (windowSize : Nat)
    (hlit : List.foldl (fun acc (s : ZstdSequence) => acc + s.literalLength) 0
              sequences.toList ≤ literals.size)
    (hvalid : ValidOffsetHistory offsetHistory)
    (hoffsets : OffsetsValidForLoop sequences.toList offsetHistory 0 windowSize)
    (hws : windowSize > 0)
    (hout : windowPrefix.size ≥ windowSize) :
    ∃ blockOutput history',
      executeSequences sequences literals windowPrefix offsetHistory windowSize
        = .ok (blockOutput, history') := by
  unfold executeSequences
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure]
  have ⟨output', history', litPos', hloop⟩ :=
    executeSequences_loop_succeeds sequences.toList literals windowPrefix
      offsetHistory 0 windowSize (by simpa using hlit) hvalid hoffsets hws hout
  rw [hloop]
  exact ⟨_, _, rfl⟩

end Zstd.Spec.Sequence
