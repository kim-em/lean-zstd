import Zstd.Spec.Fse.Basic

/-!
# FSE `probs ≥ -1` invariant

The probability bound invariant: `decodeFseDistribution` and its helpers
preserve `∀ i, probs[i].toInt ≥ -1`. This feeds into the
`ValidDistribution` predicate and is a prerequisite for
`decodeFseDistribution_sum_correct`.
-/

namespace Zstd.Spec.Fse

open ZipCommon (BitReader)

/-! ## Probability bound invariant: all probs ≥ -1 -/

/-- Pushing a value with `.toInt ≥ -1` preserves the `∀ i, arr[i].toInt ≥ -1` property. -/
private theorem push_preserves_ge_neg1
    {arr : Array Int32} {v : Int32}
    (hall : ∀ i : Fin arr.size, arr[i].toInt ≥ -1)
    (hv : v.toInt ≥ -1) :
    ∀ i : Fin (arr.push v).size, (arr.push v)[i].toInt ≥ -1 := by
  intro ⟨i, hi⟩
  simp only [Array.size_push] at hi
  by_cases hlt : i < arr.size
  · show (arr.push v)[i].toInt ≥ -1
    simp only [Array.getElem_push_lt (h := hlt)]
    exact hall ⟨i, hlt⟩
  · have heq : i = arr.size := by omega
    subst heq
    show (arr.push v)[arr.size].toInt ≥ -1
    rw [Array.getElem_push_eq]; exact hv

open Zstd.Native in
/-- `pushZeros` only pushes `0`, so `∀ i, probs[i].toInt ≥ -1` is preserved. -/
theorem pushZeros_probs_ge_neg1 (probs : Array Int32) (sym n ms : Nat)
    (hbase : ∀ i : Fin probs.size, probs[i].toInt ≥ -1) :
    ∀ i : Fin (pushZeros probs sym n ms).1.size,
      (pushZeros probs sym n ms).1[i].toInt ≥ -1 := by
  induction n generalizing probs sym with
  | zero => exact hbase
  | succ n ih =>
    change ∀ i : Fin (if sym < ms then pushZeros (probs.push 0) (sym + 1) n ms
        else (probs, sym)).1.size,
      (if sym < ms then pushZeros (probs.push 0) (sym + 1) n ms
        else (probs, sym)).1[i].toInt ≥ -1
    intro ⟨i, hi⟩
    by_cases hsym : sym < ms
    · simp only [if_pos hsym] at hi ⊢
      exact ih _ _ (push_preserves_ge_neg1 hbase (by decide)) ⟨i, hi⟩
    · simp only [if_neg hsym] at hi ⊢
      exact hbase ⟨i, hi⟩

open Zstd.Native in
/-- `decodeZeroRepeats` only pushes zeros, so `∀ i, probs[i].toInt ≥ -1` is preserved. -/
theorem decodeZeroRepeats_probs_ge_neg1
    {br : BitReader} {probs : Array Int32} {sym ms : Nat}
    {probs' : Array Int32} {sym' : Nat} {br' : BitReader}
    (h : decodeZeroRepeats br probs sym ms = .ok (probs', sym', br'))
    (hbase : ∀ i : Fin probs.size, probs[i].toInt ≥ -1) :
    ∀ i : Fin probs'.size, probs'[i].toInt ≥ -1 := by
  suffices aux : ∀ (br : BitReader) (probs : Array Int32) (sym : Nat)
      (_ : ∀ i : Fin probs.size, probs[i].toInt ≥ -1),
      ∀ {probs' : Array Int32} {sym' : Nat} {br' : BitReader},
      decodeZeroRepeats br probs sym ms = .ok (probs', sym', br') →
      ∀ i : Fin probs'.size, probs'[i].toInt ≥ -1 from aux _ _ _ hbase h
  intro br probs sym hbase
  induction br, probs, sym using decodeZeroRepeats.induct (maxSymbols := ms) with
  | case1 br probs sym e hread =>
    intro _ _ _ h; rw [decodeZeroRepeats.eq_def, hread] at h; exact nomatch h
  | case2 br probs sym repeatBits br₁ hread repeatCount probs₁ sym₁ hpush hcnt hadv =>
    rename_i ih
    intro _ _ _ h
    have hpush' : pushZeros probs sym repeatBits.toNat ms = (probs₁, sym₁) := hpush
    have hcnt' : (repeatBits.toNat == 3) = true := hcnt
    have hpz : ∀ i : Fin probs₁.size, probs₁[i].toInt ≥ -1 := by
      have hh := pushZeros_probs_ge_neg1 probs sym repeatBits.toNat ms hbase
      have heq : probs₁ = (pushZeros probs sym repeatBits.toNat ms).1 :=
        (congrArg Prod.fst hpush').symm
      rw [heq]; exact hh
    rw [decodeZeroRepeats.eq_def, hread] at h
    simp only [hpush', hcnt', ↓reduceIte, hadv, ↓reduceDIte] at h
    exact ih hpz h
  | case3 br probs sym repeatBits br₁ hread repeatCount probs₁ sym₁ hpush hcnt =>
    rename_i hadv
    intro _ _ _ h
    have hpush' : pushZeros probs sym repeatBits.toNat ms = (probs₁, sym₁) := hpush
    have hcnt' : (repeatBits.toNat == 3) = true := hcnt
    rw [decodeZeroRepeats.eq_def, hread] at h
    simp only [hcnt', ↓reduceIte, hadv, ↓reduceDIte, reduceCtorEq] at h
  | case4 br probs sym repeatBits br₁ hread repeatCount probs₁ sym₁ hpush =>
    rename_i hcnt
    intro _ _ _ h
    have hpush' : pushZeros probs sym repeatBits.toNat ms = (probs₁, sym₁) := hpush
    have hcnt' : ¬((repeatBits.toNat == 3) = true) := hcnt
    have hpz : ∀ i : Fin probs₁.size, probs₁[i].toInt ≥ -1 := by
      have hh := pushZeros_probs_ge_neg1 probs sym repeatBits.toNat ms hbase
      have heq : probs₁ = (pushZeros probs sym repeatBits.toNat ms).1 :=
        (congrArg Prod.fst hpush').symm
      rw [heq]; exact hh
    rw [decodeZeroRepeats.eq_def, hread] at h
    simp only [hpush', hcnt'] at h
    obtain ⟨rfl, _, _⟩ := h
    exact hpz

/-- `readBit` returns a value that is 0 or 1, since it masks with `&&& 1`. -/
private theorem readBit_value_lt_2 {br : ZipCommon.BitReader} {val : UInt32}
    {br' : ZipCommon.BitReader}
    (h : br.readBit = .ok (val, br')) : val.toNat < 2 := by
  unfold ZipCommon.BitReader.readBit at h
  split at h
  · exact nomatch h
  · dsimp only at h
    split at h <;> (obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj h))
    all_goals
      simp only [UInt32.toNat_and, UInt32.toNat_ofNat]
      exact Nat.lt_of_le_of_lt Nat.and_le_right (by omega)

/-- The inner accumulation loop of forward `BitReader.readBits` produces
    a value less than `2^(shift + k)` when the accumulator starts below `2^shift`.
    Each step OR's a single bit at position `shift + i`, preserving the bound. -/
private theorem readBits_go_value_lt_pow2 (br : ZipCommon.BitReader)
    (k shift : Nat) (acc val : UInt32) (br' : ZipCommon.BitReader)
    (hacc : acc.toNat < 2 ^ shift)
    (hshift : shift + k ≤ 32)
    (h : ZipCommon.BitReader.readBits.go br acc shift k = .ok (val, br')) :
    val.toNat < 2 ^ (shift + k) := by
  induction k generalizing br acc shift with
  | zero =>
    simp only [ZipCommon.BitReader.readBits.go] at h
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj h)
    simpa only [Nat.add_zero] using hacc
  | succ k ih =>
    simp only [ZipCommon.BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => rw [hrb] at h; exact nomatch h
    | ok bv =>
      rw [hrb] at h
      rw [show shift + (k + 1) = shift + 1 + k from by omega]
      refine ih _ _ _ ?_ (by omega) h
      -- acc' = acc ||| (bit <<< shift), need acc'.toNat < 2^(shift + 1)
      have hbit : bv.1.toNat < 2 := readBit_value_lt_2 hrb
      rw [UInt32.toNat_or]
      apply Nat.or_lt_two_pow
      · calc acc.toNat < 2 ^ shift := hacc
          _ ≤ 2 ^ (shift + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      · simp only [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]
        have hmod32 : shift.toUInt32.toNat % 32 = shift := by
          change (BitVec.ofNat 32 shift).toNat % 32 = shift
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : shift < 2 ^ 32)]
          exact Nat.mod_eq_of_lt (by omega : shift < 32)
        rw [hmod32]
        calc bv.1.toNat * 2 ^ shift % 2 ^ 32
            ≤ bv.1.toNat * 2 ^ shift := Nat.mod_le _ _
          _ < 2 * 2 ^ shift := (Nat.mul_lt_mul_right (Nat.pow_pos (by omega))).mpr hbit
          _ = 2 ^ (shift + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

open Zstd.Native in
/-- Reading `n` bits from a forward bitstream produces a value less than `2^n`,
    provided `n ≤ 32`. -/
theorem fwd_readBits_value_lt_pow2 (br : BitReader) (n : Nat) (val : UInt32)
    (br' : BitReader) (hn : n ≤ 32)
    (h : br.readBits n = .ok (val, br')) :
    val.toNat < 2 ^ n := by
  simp only [BitReader.readBits] at h
  have := readBits_go_value_lt_pow2 br n 0 0 val br'
    (by simp only [UInt32.toNat_zero]; omega) (by omega) h
  simpa only [Nat.zero_add] using this

open Zstd.Native in
/-- `readProbValue` returns a value ≤ `remaining + 1`. This follows from the
    variable-length encoding structure: all decoded values are at most
    `maxVal = remaining + 1`. -/
theorem readProbValue_le {br : BitReader} {remaining : Nat}
    {val : Nat} {br' : BitReader}
    (h : readProbValue br remaining = .ok (val, br'))
    (hrem : remaining < 2 ^ 31) :
    val ≤ remaining + 1 := by
  simp only [readProbValue, bind, Except.bind, pure, Except.pure] at h
  cases hrb : br.readBits (Nat.log2 (remaining + 1) + 1 - 1) with
  | error e => simp only [hrb, reduceCtorEq] at h
  | ok rawVal =>
    simp only [hrb] at h
    have hlog_le : Nat.log2 (remaining + 1) + 1 - 1 ≤ 32 := by
      have : Nat.log2 (remaining + 1) < 32 := (Nat.log2_lt (by omega)).mpr (by omega)
      omega
    have hraw := fwd_readBits_value_lt_pow2 br _ rawVal.1 rawVal.2 hlog_le hrb
    simp only [Nat.add_sub_cancel] at hraw
    -- hraw : rawVal.fst.toNat < 2 ^ Nat.log2 (remaining + 1)
    -- Convert 1 <<< k to 2 ^ k in all hypotheses before case split
    have hshift : ∀ k, 1 <<< k = 2 ^ k := fun k => by
      simp only [Nat.shiftLeft_eq, Nat.one_mul]
    simp only [hshift, Nat.add_sub_cancel, Nat.pow_succ] at *
    -- Establish 2^L ≤ remaining + 1 for all cases
    have hle_p : 2 ^ Nat.log2 (remaining + 1) ≤ remaining + 1 :=
      Nat.log2_self_le (by omega)
    split at h
    · -- rawBits < lowThreshold: returns rawBits
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      -- rawBits < 2^L ≤ remaining + 1 → rawBits ≤ remaining
      have := Nat.lt_of_lt_of_le hraw hle_p
      omega
    · -- rawBits ≥ lowThreshold: reads extra bit
      cases hrb2 : rawVal.2.readBits 1 with
      | error e => simp only [hrb2, reduceCtorEq] at h
      | ok extraVal =>
        simp only [hrb2] at h
        split at h
        · -- extraBit == 0: returns rawBits
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          have := Nat.lt_of_lt_of_le hraw hle_p
          omega
        · -- extraBit == 1: returns rawBits + threshold - lowThreshold
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, _⟩ := h
          have hlt_2p : remaining + 1 < 2 ^ (Nat.log2 (remaining + 1) + 1) := Nat.lt_log2_self
          simp only [Nat.pow_succ] at *
          generalize 2 ^ Nat.log2 (remaining + 1) = p at *
          omega

/-- `Int32.ofNat n - 1` has `.toInt ≥ -1` when `n < 2^31`. -/
private theorem int32_ofNat_sub_one_ge_neg1 {n : Nat} (hn : n < 2 ^ 31) :
    (Int32.ofNat n - 1).toInt ≥ -1 := by
  by_cases h0 : n = 0
  · subst h0; decide
  · -- Reduce to BitVec level: Int32/UInt32 subtraction is definitionally BitVec subtraction
    change (BitVec.ofNat 32 n - BitVec.ofNat 32 1).toInt ≥ -1
    simp only [BitVec.toInt, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

open Zstd.Native in
/-- Main loop preserves `∀ i, probs[i].toInt ≥ -1`: each case either pushes
    `0` (via decodeZeroRepeats), `-1`, or `Int32.ofNat val - 1` where
    `Int32.ofNat val ≥ 0` (guaranteed by `rem < 2^31` and `readProbValue_le`).
    The precondition `rem < 2^31` is satisfied by all Zstd FSE distributions
    (accuracy log ≤ 9, so remaining ≤ 512). -/
theorem decodeFseLoop_probs_ge_neg1
    {br : BitReader} {rem : Nat} {probs : Array Int32}
    {sym ms fuel : Nat}
    {rem' : Nat} {probs' : Array Int32} {sym' : Nat} {br' : BitReader}
    (h : decodeFseLoop br rem probs sym ms fuel = .ok (rem', probs', sym', br'))
    (hbase : ∀ i : Fin probs.size, probs[i].toInt ≥ -1)
    (hrem : rem + 1 < 2 ^ 31) :
    ∀ i : Fin probs'.size, probs'[i].toInt ≥ -1 := by
  induction fuel generalizing br rem probs sym with
  | zero => simp only [decodeFseLoop, reduceCtorEq] at h
  | succ fuel ih =>
    rw [decodeFseLoop.eq_2] at h
    by_cases hcond : ¬(rem > 0 ∧ sym < ms)
    · rw [if_pos hcond] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl, _, _⟩ := h; exact hbase
    · rw [if_neg hcond] at h
      cases hrpv : readProbValue br rem with
      | error e => simp only [hrpv, reduceCtorEq] at h
      | ok val =>
        simp only [hrpv] at h
        have hval_le := readProbValue_le hrpv (by omega)
        by_cases hp0 : (Int32.ofNat val.fst - 1 == 0) = true
        · rw [if_pos hp0] at h
          cases hzr : decodeZeroRepeats val.2 (probs.push 0) (sym + 1) ms with
          | error e => simp only [hzr, reduceCtorEq] at h
          | ok val₂ =>
            simp only [hzr] at h
            have hpush := push_preserves_ge_neg1 hbase (show (0 : Int32).toInt ≥ -1 from by decide)
            exact ih h (decodeZeroRepeats_probs_ge_neg1 hzr hpush) (by omega)
        · rw [if_neg hp0] at h
          by_cases hp1 : (Int32.ofNat val.fst - 1 == -1) = true
          · rw [if_pos hp1] at h
            exact ih h (push_preserves_ge_neg1 hbase (by simp [eq_of_beq hp1])) (by omega)
          · rw [if_neg hp1] at h
            by_cases hgt : int32ToNat (Int32.ofNat val.fst - 1) > rem
            · rw [if_pos hgt] at h; exact nomatch h
            · rw [if_neg hgt] at h
              have hv : (Int32.ofNat val.fst - 1).toInt ≥ -1 :=
                int32_ofNat_sub_one_ge_neg1 (by omega)
              exact ih h (push_preserves_ge_neg1 hbase hv) (by omega)

end Zstd.Spec.Fse
