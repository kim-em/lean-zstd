import Zstd.Native.Fse

/-!
# BackwardBitReader specs

Foundational specs for `Zstd.Native.BackwardBitReader`:
- `isFinished` characterization
- `readBits` value bound, total-bits tracking, field preservation
- `init` specs and completeness
-/

namespace Zstd.Spec.Fse

/-! ## BackwardBitReader base-case specs -/

open Zstd.Native (BackwardBitReader) in
/-- `isFinished` is true iff `totalBitsRemaining` is zero. -/
theorem BackwardBitReader_isFinished_iff_totalBitsRemaining_zero
    (br : BackwardBitReader) :
    br.isFinished = true ↔ br.totalBitsRemaining = 0 := by
  simp only [BackwardBitReader.isFinished, BackwardBitReader.totalBitsRemaining]
  constructor
  · intro h; simp only [beq_iff_eq.mp h, BEq.rfl, ↓reduceIte]
  · intro h
    split at h
    · assumption
    · -- bitsRemaining + 8 * (bytePos - startPos) = 0 contradicts ¬(bitsRemaining == 0)
      rename_i hne
      simp only [beq_iff_eq, Nat.add_eq_zero_iff] at hne h
      exact absurd h.1 hne

open Zstd.Native (BackwardBitReader) in
/-- Reading 0 bits is a no-op: returns (0, br) unchanged. -/
theorem readBits_zero (br : BackwardBitReader) :
    br.readBits 0 = .ok (0, br) := by
  simp only [BackwardBitReader.readBits, BackwardBitReader.readBits.go]

open Zstd.Native (BackwardBitReader) in
/-- Reading n > 0 bits from a finished reader always errors. -/
theorem readBits_error_of_isFinished (br : BackwardBitReader) (n : Nat)
    (hn : n > 0) (hfin : br.isFinished = true) :
    ∃ e, br.readBits n = .error e := by
  match n, hn with
  | k + 1, _ =>
  simp only [BackwardBitReader.isFinished, beq_iff_eq] at hfin
  simp only [BackwardBitReader.readBits, BackwardBitReader.readBits.go, hfin]
  exact ⟨_, rfl⟩

/-! ## BackwardBitReader value bound -/

/-- Shifting a UInt32 left by 1 and OR-ing with a UInt8 masked to 1 bit
    produces a value less than `2^(m+1)` when the original is less than `2^m`. -/
private theorem uint32_shift_or_bit_bound (acc : UInt32) (byte : UInt8) (pos : UInt8)
    (m : Nat)
    (hacc : acc.toNat < 2 ^ m) :
    (acc <<< 1 ||| (byte >>> pos &&& 1).toUInt32).toNat < 2 ^ (m + 1) := by
  -- The result is always < 2^32, so if m+1 ≥ 32, the bound is trivial
  by_cases hm : m + 1 ≥ 32
  · calc (acc <<< 1 ||| (byte >>> pos &&& 1).toUInt32).toNat
        < 2 ^ 32 := UInt32.toNat_lt _
      _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by omega) hm
  · -- m + 1 < 32, so m ≤ 30 and the result fits in 31 bits
    have hm' : m ≤ 30 := by omega
    -- Split into components
    -- Use Nat.or_lt_two_pow: if both operands < 2^(m+1), their OR is too
    rw [UInt32.toNat_or]
    apply Nat.or_lt_two_pow
    · -- (acc <<< 1).toNat < 2^(m+1)
      simp only [UInt32.toNat_shiftLeft, Nat.shiftLeft_eq]
      have : (1 : UInt32).toNat % 32 = 1 := by decide
      rw [this, Nat.pow_one, Nat.mod_eq_of_lt]
      · rw [Nat.pow_succ]; omega
      · calc acc.toNat * 2
            < 2 ^ m * 2 := by omega
          _ = 2 ^ (m + 1) := by rw [Nat.pow_succ]
          _ ≤ 2 ^ 31 := Nat.pow_le_pow_right (by omega) (by omega)
          _ < 2 ^ 32 := by omega
    · -- (byte >>> pos &&& 1).toUInt32.toNat < 2^(m+1)
      simp only [UInt8.toNat_toUInt32, UInt8.toNat_and, UInt8.toNat_shiftRight,
        UInt8.reduceToNat, Nat.and_one_is_mod]
      omega

open Zstd.Native (BackwardBitReader) in
/-- The inner loop of `readBits` maintains the value bound: if the accumulator
    starts below `2^(n-k)`, the final value is below `2^n`. -/
private theorem readBits_go_value_bound {n : Nat} (br : BackwardBitReader) (k : Nat)
    (acc : UInt32) (val : UInt32) (br' : BackwardBitReader)
    (hkn : k ≤ n)
    (hacc : acc.toNat < 2 ^ (n - k))
    (h : BackwardBitReader.readBits.go br k acc = .ok (val, br')) :
    val.toNat < 2 ^ n := by
  induction k generalizing br acc with
  | zero =>
    simp only [BackwardBitReader.readBits.go] at h
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Except.ok.inj h)
    simpa only [Nat.sub_zero] using hacc
  | succ k ih =>
    simp only [BackwardBitReader.readBits.go, bind, Except.bind] at h
    split at h
    · exact nomatch h
    · simp only [pure, Except.pure] at h
      refine ih _ _ (by omega) ?_ h
      have hne : n - k = (n - (k + 1)) + 1 := by omega
      rw [hne]
      exact uint32_shift_or_bit_bound acc _ _ _ hacc

open Zstd.Native (BackwardBitReader) in
/-- Reading `n` bits from a backward bitstream produces a value less than `2^n`. -/
theorem readBits_value_lt_pow2 (br : BackwardBitReader) (n : Nat)
    (val : UInt32) (br' : BackwardBitReader)
    (h : br.readBits n = .ok (val, br')) :
    val.toNat < 2 ^ n := by
  simp only [BackwardBitReader.readBits] at h
  exact readBits_go_value_bound br n 0 val br' (Nat.le_refl n) (by simp) h

/-! ## BackwardBitReader totalBitsRemaining tracking -/

open Zstd.Native (BackwardBitReader) in
/-- The recursive helper `readBits.go` decreases `totalBitsRemaining` by exactly `k`. -/
private theorem readBits_go_totalBitsRemaining (br : BackwardBitReader)
    (k : Nat) (acc val : UInt32) (br' : BackwardBitReader)
    (h : BackwardBitReader.readBits.go br k acc = .ok (val, br')) :
    br'.totalBitsRemaining = br.totalBitsRemaining - k := by
  induction k generalizing br acc with
  | zero =>
    simp only [BackwardBitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    omega
  | succ k ih =>
    simp only [BackwardBitReader.readBits.go, bind, Except.bind] at h
    split at h
    · exact nomatch h
    · simp only [pure, Except.pure] at h
      rename_i hbr_ne; simp only [beq_iff_eq] at hbr_ne
      rw [ih _ _ h]
      simp only [BackwardBitReader.totalBitsRemaining, beq_iff_eq]
      by_cases h1 : br.bitsRemaining - 1 = 0 <;> by_cases h2 : br.bytePos > br.startPos <;>
        simp only [h1, h2, hbr_ne, show ¬((8 : Nat) = 0) from by omega, ↓reduceIte] <;> omega

open Zstd.Native (BackwardBitReader) in
/-- When `readBits.go` succeeds, the initial reader had enough bits. -/
private theorem readBits_go_totalBitsRemaining_ge (br : BackwardBitReader)
    (k : Nat) (acc val : UInt32) (br' : BackwardBitReader)
    (h : BackwardBitReader.readBits.go br k acc = .ok (val, br')) :
    br.totalBitsRemaining ≥ k := by
  induction k generalizing br acc with
  | zero => omega
  | succ k ih =>
    simp only [BackwardBitReader.readBits.go, bind, Except.bind] at h
    split at h
    · exact nomatch h
    · simp only [pure, Except.pure] at h
      rename_i hbr_ne; simp only [beq_iff_eq] at hbr_ne
      have hrec := ih _ _ h
      simp only [BackwardBitReader.totalBitsRemaining, beq_iff_eq] at hrec ⊢
      by_cases h1 : br.bitsRemaining - 1 = 0 <;> by_cases h2 : br.bytePos > br.startPos <;>
        simp only [h1, h2, hbr_ne, show ¬((8 : Nat) = 0) from by omega, ↓reduceIte] at hrec ⊢
          <;> omega

open Zstd.Native (BackwardBitReader) in
/-- Reading `n` bits from a backward bitstream decreases `totalBitsRemaining`
    by exactly `n`. -/
theorem readBits_totalBitsRemaining_sub (br : BackwardBitReader)
    (n : Nat) (val : UInt32) (br' : BackwardBitReader)
    (h : br.readBits n = .ok (val, br')) :
    br'.totalBitsRemaining = br.totalBitsRemaining - n := by
  simp only [BackwardBitReader.readBits] at h
  exact readBits_go_totalBitsRemaining br n 0 val br' h

open Zstd.Native (BackwardBitReader) in
/-- When reading a positive number of bits succeeds, `totalBitsRemaining`
    strictly decreases. -/
theorem readBits_totalBitsRemaining_lt (br : BackwardBitReader)
    (n : Nat) (val : UInt32) (br' : BackwardBitReader)
    (hn : n > 0) (h : br.readBits n = .ok (val, br')) :
    br'.totalBitsRemaining < br.totalBitsRemaining := by
  simp only [BackwardBitReader.readBits] at h
  have hsub := readBits_go_totalBitsRemaining br n 0 val br' h
  have hge := readBits_go_totalBitsRemaining_ge br n 0 val br' h
  omega

/-! ## BackwardBitReader.init specs -/

open Zstd.Native (BackwardBitReader) in
/-- When `highBitPos b = some p`, the position is less than 8. -/
private theorem highBitPos_lt_eight (b : UInt8) (p : Nat)
    (h : BackwardBitReader.highBitPos b = some p) : p < 8 := by
  unfold BackwardBitReader.highBitPos at h; grind

open Zstd.Native (BackwardBitReader) in
/-- Successful `init` preserves the `startPos` argument. -/
theorem BackwardBitReader_init_startPos_eq (data : ByteArray)
    (startPos endPos : Nat) (br : BackwardBitReader)
    (h : BackwardBitReader.init data startPos endPos = .ok br) :
    br.startPos = startPos := by
  simp only [BackwardBitReader.init, bind, Except.bind, pure, Except.pure] at h
  split at h; · exact nomatch h
  split at h; · exact nomatch h
  split at h; · exact nomatch h
  split at h
  · split at h <;> (obtain rfl := Except.ok.inj h; rfl)
  · obtain rfl := Except.ok.inj h; rfl

open Zstd.Native (BackwardBitReader) in
/-- The initial `totalBitsRemaining` is strictly less than `8 * (endPos - startPos)`.
    This is because the sentinel bit itself is consumed during initialization. -/
theorem BackwardBitReader_init_totalBitsRemaining_lt (data : ByteArray)
    (startPos endPos : Nat) (br : BackwardBitReader)
    (h : BackwardBitReader.init data startPos endPos = .ok br) :
    br.totalBitsRemaining < 8 * (endPos - startPos) := by
  simp only [BackwardBitReader.init, bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · rename_i hle
    split at h
    · exact nomatch h
    · rename_i hsize
      split at h
      · exact nomatch h
      · rename_i sentinelPos
        split at h
        · rename_i hsp; simp only [beq_iff_eq] at hsp
          split at h <;> (obtain rfl := Except.ok.inj h) <;>
            simp only [BackwardBitReader.totalBitsRemaining, beq_iff_eq,
              show ¬(8 : Nat) = 0 from by omega, ↓reduceIte] <;> omega
        · rename_i hsp; simp only [beq_iff_eq] at hsp
          obtain rfl := Except.ok.inj h
          simp only [BackwardBitReader.totalBitsRemaining, beq_iff_eq, hsp, ↓reduceIte]
          have hlt := highBitPos_lt_eight _ _ ‹_›
          omega

/-! ## BackwardBitReader field preservation -/

open Zstd.Native (BackwardBitReader) in
/-- The recursive helper `readBits.go` preserves the `data` field. -/
private theorem readBits_go_data_eq (br : BackwardBitReader)
    (k : Nat) (acc val : UInt32) (br' : BackwardBitReader)
    (h : BackwardBitReader.readBits.go br k acc = .ok (val, br')) :
    br'.data = br.data := by
  induction k generalizing br acc with
  | zero =>
    simp only [BackwardBitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Except.ok.inj h); rfl
  | succ k ih =>
    simp only [BackwardBitReader.readBits.go, bind, Except.bind] at h
    split at h; · exact nomatch h
    simp only [pure, Except.pure] at h; rw [ih _ _ h]
    split <;> (try split) <;> rfl

open Zstd.Native (BackwardBitReader) in
/-- Reading `n` bits from a backward bitstream preserves the `data` field. -/
theorem readBits_data_eq (br : BackwardBitReader) (n : Nat)
    (val : UInt32) (br' : BackwardBitReader)
    (h : br.readBits n = .ok (val, br')) :
    br'.data = br.data := by
  simp only [BackwardBitReader.readBits] at h
  exact readBits_go_data_eq br n 0 val br' h

open Zstd.Native (BackwardBitReader) in
/-- The recursive helper `readBits.go` preserves the `startPos` field. -/
private theorem readBits_go_startPos_eq (br : BackwardBitReader)
    (k : Nat) (acc val : UInt32) (br' : BackwardBitReader)
    (h : BackwardBitReader.readBits.go br k acc = .ok (val, br')) :
    br'.startPos = br.startPos := by
  induction k generalizing br acc with
  | zero =>
    simp only [BackwardBitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Except.ok.inj h); rfl
  | succ k ih =>
    simp only [BackwardBitReader.readBits.go, bind, Except.bind] at h
    split at h; · exact nomatch h
    simp only [pure, Except.pure] at h; rw [ih _ _ h]
    split <;> (try split) <;> rfl

open Zstd.Native (BackwardBitReader) in
/-- Reading `n` bits from a backward bitstream preserves the `startPos` field. -/
theorem readBits_startPos_eq (br : BackwardBitReader) (n : Nat)
    (val : UInt32) (br' : BackwardBitReader)
    (h : br.readBits n = .ok (val, br')) :
    br'.startPos = br.startPos := by
  simp only [BackwardBitReader.readBits] at h
  exact readBits_go_startPos_eq br n 0 val br' h

open Zstd.Native (BackwardBitReader) in
/-- Successful `init` sets the `data` field to the input data. -/
theorem BackwardBitReader_init_data_eq (data : ByteArray)
    (startPos endPos : Nat) (br : BackwardBitReader)
    (h : BackwardBitReader.init data startPos endPos = .ok br) :
    br.data = data := by
  simp only [BackwardBitReader.init, bind, Except.bind, pure, Except.pure] at h
  split at h; · exact nomatch h
  split at h; · exact nomatch h
  split at h; · exact nomatch h
  split at h
  · split at h <;> (obtain rfl := Except.ok.inj h; rfl)
  · obtain rfl := Except.ok.inj h; rfl

/-! ## BackwardBitReader.init completeness -/

open Zstd.Native (BackwardBitReader) in
/-- When a byte is nonzero, `highBitPos` returns `some`. -/
theorem highBitPos_some_of_ne_zero (b : UInt8) (hb : b ≠ 0) :
    ∃ n, BackwardBitReader.highBitPos b = some n := by
  unfold BackwardBitReader.highBitPos
  simp only [bne_iff_ne, ne_eq, beq_iff_eq, hb, ↓reduceIte]
  repeat (first | exact ⟨_, rfl⟩ | split)

open Zstd.Native (BackwardBitReader) in
/-- When `startPos < endPos`, `endPos ≤ data.size`, and the last byte is nonzero,
    `BackwardBitReader.init` succeeds. -/
theorem BackwardBitReader_init_succeeds (data : ByteArray)
    (startPos endPos : Nat)
    (hrange : startPos < endPos)
    (hsize : endPos ≤ data.size)
    (hlast : data[endPos - 1]! ≠ 0) :
    ∃ br, BackwardBitReader.init data startPos endPos = .ok br := by
  simp only [BackwardBitReader.init, bind, Except.bind, pure, Except.pure]
  rw [if_neg (by omega), if_neg (by omega)]
  obtain ⟨n, hn⟩ := highBitPos_some_of_ne_zero _ hlast
  simp only [hn]; split <;> (try split) <;> exact ⟨_, rfl⟩

end Zstd.Spec.Fse
