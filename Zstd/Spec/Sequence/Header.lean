import Zstd.Native.Sequence

/-!
# `parseSequencesHeader` structural properties

Position-advance bounds, sequence-count formulas, and completeness of the
sequence section header parser (RFC 8878 §3.1.1.3.2). Every branch reads
1–4 bytes depending on `byte0`; the theorems characterize the results
branch by branch and unify them.
-/

namespace Zstd.Native

/-! ## parseSequencesHeader structural properties -/

/-- When `parseSequencesHeader` succeeds, the returned position is strictly greater
    than the input and advances by at most 4 bytes. -/
private theorem parseSequencesHeader_pos_range (data : ByteArray) (pos : Nat)
    (numSeq : Nat) (modes : SequenceCompressionModes) (pos' : Nat)
    (h : parseSequencesHeader data pos = .ok (numSeq, modes, pos')) :
    pos < pos' ∧ pos' ≤ pos + 4 ∧ pos' ≤ data.size := by
  simp only [parseSequencesHeader, Pure.pure, Except.pure] at h
  split at h; · exact nomatch h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, -, rfl⟩ := h; omega
  · split at h
    · split at h; · exact nomatch h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, -, rfl⟩ := h; omega
    · split at h
      · split at h; · exact nomatch h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, -, rfl⟩ := h; omega
      · split at h; · exact nomatch h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨-, -, rfl⟩ := h; omega

/-- When `parseSequencesHeader` succeeds, the returned position is strictly greater
    than the input position. Each branch advances by 1–4 bytes. -/
theorem parseSequencesHeader_pos_gt (data : ByteArray) (pos : Nat)
    (numSeq : Nat) (modes : SequenceCompressionModes) (pos' : Nat)
    (h : parseSequencesHeader data pos = .ok (numSeq, modes, pos')) :
    pos' > pos :=
  (parseSequencesHeader_pos_range data pos numSeq modes pos' h).1

/-- When `parseSequencesHeader` succeeds, the position advances by at most 4 bytes.
    The maximum occurs in the 3-byte count case (byte0 = 255): 3 count bytes +
    1 modes byte. -/
theorem parseSequencesHeader_pos_bounded (data : ByteArray) (pos : Nat)
    (numSeq : Nat) (modes : SequenceCompressionModes) (pos' : Nat)
    (h : parseSequencesHeader data pos = .ok (numSeq, modes, pos')) :
    pos' ≤ pos + 4 :=
  (parseSequencesHeader_pos_range data pos numSeq modes pos' h).2.1

/-- When `parseSequencesHeader` succeeds, the returned position is within
    `data.size`. Each branch checks `data.size < pos + k` before reading `k`
    bytes, so on success `pos + k ≤ data.size` and `pos' = pos + k`. -/
theorem parseSequencesHeader_le_size (data : ByteArray) (pos : Nat)
    (numSeq : Nat) (modes : SequenceCompressionModes) (pos' : Nat)
    (h : parseSequencesHeader data pos = .ok (numSeq, modes, pos')) :
    pos' ≤ data.size :=
  (parseSequencesHeader_pos_range data pos numSeq modes pos' h).2.2

/-- When the input byte at `pos` is zero, `parseSequencesHeader` returns 0 sequences
    with predefined compression modes and advances by exactly 1 byte.
    This is the "no sequences" case (RFC 8878 §3.1.1.3.2): blocks that contain
    only literals have byte0 = 0 and no compression modes byte follows.

    Note: The converse does not hold — `parseSequencesHeader` can also return
    numSeq = 0 from the 2-byte encoding when byte0 = 128 and the next byte is 0,
    but in that case pos' = pos + 3 and modes are parsed from the data. -/
theorem parseSequencesHeader_byte0_zero (data : ByteArray) (pos : Nat)
    (hsize : pos + 1 ≤ data.size) (hbyte : data[pos]!.toNat = 0) :
    parseSequencesHeader data pos =
      .ok (0, { litLenMode := .predefined, offsetMode := .predefined,
                matchLenMode := .predefined }, pos + 1) := by
  simp only [parseSequencesHeader, Pure.pure, Except.pure]
  simp only [show ¬(data.size < pos + 1) from by omega, ↓reduceIte, dite_false,
    ← getElem!_pos, hbyte, beq_self_eq_true]

/-- When 0 < byte0 < 128, the number of sequences is exactly byte0.
    This is the 1-byte encoding (RFC 8878 §3.1.1.3.2.1) used for up to
    127 sequences, covering the vast majority of real-world Zstd frames. -/
theorem parseSequencesHeader_numSeq_small (data : ByteArray) (pos : Nat)
    (numSeq : Nat) (modes : SequenceCompressionModes) (pos' : Nat)
    (h : parseSequencesHeader data pos = .ok (numSeq, modes, pos'))
    (hbyte0_pos : data[pos]!.toNat > 0)
    (hbyte0_lt : data[pos]!.toNat < 128) :
    numSeq = data[pos]!.toNat := by
  unfold parseSequencesHeader at h
  simp only [Pure.pure, Except.pure] at h
  -- Size check
  by_cases hsz : data.size < pos + 1
  · simp only [hsz, dite_true] at h; exact nomatch h
  · simp only [hsz, dite_false, ← getElem!_pos] at h
    -- byte0 == 0 check; byte0 < 128 check
    have hbeq : ¬((data[pos]!.toNat == 0) = true) := by simp only [beq_iff_eq]; omega
    rw [if_neg hbeq, if_pos hbyte0_lt] at h
    -- Inner size check
    by_cases hsz2 : data.size < pos + 2
    · simp only [hsz2, dite_true] at h; exact nomatch h
    · simp only [hsz2, dite_false, Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm

/-- When 128 ≤ byte0 < 255, the number of sequences uses the 2-byte encoding:
    `numSeq = ((byte0 - 128) << 8) + byte1` (RFC 8878 §3.1.1.3.2.1).
    This covers sequence counts from 128 to 32511. -/
theorem parseSequencesHeader_numSeq_medium (data : ByteArray) (pos : Nat)
    (numSeq : Nat) (modes : SequenceCompressionModes) (pos' : Nat)
    (h : parseSequencesHeader data pos = .ok (numSeq, modes, pos'))
    (hbyte0_ge : data[pos]!.toNat ≥ 128)
    (hbyte0_lt : data[pos]!.toNat < 255) :
    numSeq = ((data[pos]!.toNat - 128) <<< 8) + data[pos + 1]!.toNat := by
  unfold parseSequencesHeader at h
  simp only [Pure.pure, Except.pure] at h
  -- Size check
  by_cases hsz : data.size < pos + 1
  · simp only [hsz, dite_true] at h; exact nomatch h
  · simp only [hsz, dite_false, ← getElem!_pos] at h
    -- byte0 == 0 check; byte0 ≥ 128 check; byte0 < 255 check
    have hbeq : ¬((data[pos]!.toNat == 0) = true) := by simp only [beq_iff_eq]; omega
    have hlt128 : ¬(data[pos]!.toNat < 128) := by omega
    rw [if_neg hbeq, if_neg hlt128, if_pos hbyte0_lt] at h
    -- Inner size check
    by_cases hsz2 : data.size < pos + 3
    · simp only [hsz2, dite_true] at h; exact nomatch h
    · simp only [hsz2, dite_false, Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm

/-- For the 1-byte encoding (byte0 < 128), numSeq = 0 iff byte0 = 0.
    Completes the characterization of zero vs positive sequence counts
    when byte0 < 128. The 2-byte case (byte0 ≥ 128) can yield numSeq = 0
    with byte0 ≠ 0, so this iff requires the byte0 < 128 restriction. -/
theorem parseSequencesHeader_numSeq_zero_iff (data : ByteArray) (pos : Nat)
    (numSeq : Nat) (modes : SequenceCompressionModes) (pos' : Nat)
    (h : parseSequencesHeader data pos = .ok (numSeq, modes, pos'))
    (hbyte0_lt : data[pos]!.toNat < 128) :
    numSeq = 0 ↔ data[pos]!.toNat = 0 := by
  constructor
  · -- → : numSeq = 0 → byte0 = 0
    intro hzero
    by_cases hne : data[pos]!.toNat = 0
    · exact hne
    · exfalso
      have hpos : data[pos]!.toNat > 0 := by omega
      have := parseSequencesHeader_numSeq_small data pos numSeq modes pos' h hpos hbyte0_lt
      omega
  · -- ← : byte0 = 0 → numSeq = 0
    intro hbyte0
    unfold parseSequencesHeader at h
    simp only [Pure.pure, Except.pure] at h
    by_cases hsz : data.size < pos + 1
    · simp only [hsz, dite_true] at h; exact nomatch h
    · simp only [hsz, dite_false, ← getElem!_pos] at h
      have hbeq : (data[pos]!.toNat == 0) = true := beq_iff_eq.mpr hbyte0
      rw [if_pos hbeq] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.1.symm

/-! ## Parsing completeness -/

/-- When the data has at least 4 bytes from `pos`, `parseSequencesHeader` always succeeds.
    All four branches (byte0=0, byte0<128, byte0<255, byte0=255) have their size guards
    satisfied by the 4-byte hypothesis, so the result is always `.ok`. -/
theorem parseSequencesHeader_succeeds (data : ByteArray) (pos : Nat)
    (hsize : data.size ≥ pos + 4) :
    ∃ numSeq modes pos', parseSequencesHeader data pos = .ok (numSeq, modes, pos') := by
  unfold parseSequencesHeader
  simp only [Pure.pure, Except.pure,
    show ¬(data.size < pos + 1) from by omega, dite_false]
  split -- byte0 == 0
  · exact ⟨_, _, _, rfl⟩
  · split -- byte0 < 128
    · simp only [show ¬(data.size < pos + 2) from by omega, dite_false]
      exact ⟨_, _, _, rfl⟩
    · split -- byte0 < 255
      · simp only [show ¬(data.size < pos + 3) from by omega, dite_false]
        exact ⟨_, _, _, rfl⟩
      · simp only [show ¬(data.size < pos + 4) from by omega, dite_false]
        exact ⟨_, _, _, rfl⟩

/-- When `data[pos]! = 0` and there is at least 1 byte, parsing succeeds with
    0 sequences, all-predefined modes, and advances by exactly 1 byte.
    This is the "no sequences" fast path for literals-only blocks. -/
theorem parseSequencesHeader_succeeds_zero (data : ByteArray) (pos : Nat)
    (hsize : data.size ≥ pos + 1) (hbyte : data[pos]! = 0) :
    parseSequencesHeader data pos =
      .ok (0, { litLenMode := .predefined, offsetMode := .predefined,
                matchLenMode := .predefined }, pos + 1) := by
  simp only [parseSequencesHeader, Pure.pure, Except.pure]
  simp only [show ¬(data.size < pos + 1) from by omega, dite_false,
    ← getElem!_pos, show data[pos]!.toNat = 0 from by simp [hbyte], beq_self_eq_true,
    ↓reduceIte]

end Zstd.Native
