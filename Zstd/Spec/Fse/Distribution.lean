import Zstd.Spec.Fse.Basic

/-!
# FSE distribution correctness

Correctness theorems for `Zstd.Native.decodeFseDistribution` and the three
predefined distributions, relating them to the `ValidDistribution`
predicate. -/

namespace Zstd.Spec.Fse

open ZipCommon (BitReader)

/-! ## Correctness of predefined distributions -/

open Zstd.Native in
/-- The predefined literal length distribution is valid for accuracy log 6. -/
theorem predefined_litLen_valid :
    ValidDistribution predefinedLitLenDistribution 6 := by decide

open Zstd.Native in
/-- The predefined match length distribution is valid for accuracy log 6. -/
theorem predefined_matchLen_valid :
    ValidDistribution predefinedMatchLenDistribution 6 := by decide

open Zstd.Native in
/-- The predefined offset distribution is valid for accuracy log 5. -/
theorem predefined_offset_valid :
    ValidDistribution predefinedOffsetDistribution 5 := by decide

/-! ## Correctness of `decodeFseDistribution`

These theorems relate the output of `decodeFseDistribution` to the
validity predicates defined above. -/

open Zstd.Native in
/-- Decomposition of a successful `decodeFseDistribution` call. Extracts
    the readBits(4) result, the accuracy log relation, the maxAccLog bound,
    and the decodeFseLoop result with remaining = 0. -/
theorem decodeFseDistribution_ok_decompose
    {br : BitReader} {maxSymbols maxAccLog : Nat}
    {probs : Array Int32} {al : Nat} {br' : BitReader}
    (h : decodeFseDistribution br maxSymbols maxAccLog = .ok (probs, al, br')) :
    ∃ (rdval : UInt32 × BitReader) (sym' : Nat),
      br.readBits 4 = .ok rdval ∧
      al = rdval.1.toNat + 5 ∧
      al ≤ maxAccLog ∧
      decodeFseLoop rdval.2 (1 <<< al) #[] 0 maxSymbols 10000 =
        .ok (0, probs, sym', br') := by
  unfold decodeFseDistribution at h
  cases hrd : br.readBits 4 with
  | error e => simp only [hrd, reduceCtorEq] at h
  | ok val =>
    simp only [hrd] at h
    by_cases hgt : val.fst.toNat + 5 > maxAccLog
    · rw [if_pos hgt] at h; exact nomatch h
    · rw [if_neg hgt] at h
      cases hdl : decodeFseLoop val.snd (1 <<< (val.fst.toNat + 5)) #[] 0 maxSymbols 10000 with
      | error e => simp only [hdl, reduceCtorEq] at h
      | ok dlval =>
        simp only [hdl] at h
        by_cases hrem : dlval.1 != 0
        · rw [if_pos hrem] at h; exact nomatch h
        · rw [if_neg hrem] at h
          simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hrem
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          refine ⟨val, dlval.2.2.1, rfl, h.2.1.symm, by omega, ?_⟩
          rw [h.2.1.symm, hdl]; congr 1
          exact Prod.ext hrem (Prod.ext h.1 (Prod.ext rfl h.2.2))

open Zstd.Native in
/-- When `decodeFseDistribution` succeeds, the returned accuracy log is
    at least 5. This follows from the computation `accuracyLog = readBits(4) + 5`
    where `readBits(4)` returns a non-negative value. -/
theorem decodeFseDistribution_accuracyLog_ge
    {br : BitReader} {maxSymbols maxAccLog : Nat}
    {probs : Array Int32} {al : Nat} {br' : BitReader}
    (_h : decodeFseDistribution br maxSymbols maxAccLog = .ok (probs, al, br')) :
    5 ≤ al := by
  obtain ⟨_, _, _, hal, _, _⟩ := decodeFseDistribution_ok_decompose _h; omega

open Zstd.Native in
/-- When `decodeFseDistribution` succeeds, the returned accuracy log does
    not exceed `maxAccLog`. This follows from the guard
    `if accuracyLog > maxAccLog then throw ...`. -/
theorem decodeFseDistribution_accuracyLog_le
    {br : BitReader} {maxSymbols maxAccLog : Nat}
    {probs : Array Int32} {al : Nat} {br' : BitReader}
    (_h : decodeFseDistribution br maxSymbols maxAccLog = .ok (probs, al, br')) :
    al ≤ maxAccLog := by
  obtain ⟨_, _, _, _, hle, _⟩ := decodeFseDistribution_ok_decompose _h; exact hle

open Zstd.Native in
/-- When `decodeFseDistribution` succeeds, the cell count of the returned
    distribution equals `1 << al`. This follows from the `remaining == 0`
    check at the end of the function: `remaining` starts at `1 << al` and
    is decremented by each probability value. -/
theorem decodeFseDistribution_sum_correct
    {br : BitReader} {maxSymbols maxAccLog : Nat}
    {probs : Array Int32} {al : Nat} {br' : BitReader}
    (_h : decodeFseDistribution br maxSymbols maxAccLog = .ok (probs, al, br')) :
    cellCount probs = 1 <<< al := by
  obtain ⟨_, _, _, _, _, hdl⟩ := decodeFseDistribution_ok_decompose _h
  have hinv := decodeFseLoop_invariant hdl
  simp only [cellCount_empty, Nat.add_zero] at hinv; omega

open Zstd.Native in
/-- When `decodeFseDistribution` succeeds, the returned probability array is
    non-empty. This follows from `cellCount probs = 1 <<< al` (sum_correct)
    and `al ≥ 5` (accuracyLog_ge): an empty array has cellCount 0, but
    `1 <<< al ≥ 32 > 0`. -/
theorem decodeFseDistribution_size_pos
    {br : BitReader} {maxSymbols maxAccLog : Nat}
    {probs : Array Int32} {al : Nat} {br' : BitReader}
    (h : decodeFseDistribution br maxSymbols maxAccLog = .ok (probs, al, br')) :
    0 < probs.size := by
  have hcc := decodeFseDistribution_sum_correct h
  have hal := decodeFseDistribution_accuracyLog_ge h
  have hne : probs.size ≠ 0 := by
    intro hsz
    have : probs = #[] := Array.ext (by simp [hsz]) (fun i h1 _ => absurd h1 (by omega))
    rw [this, cellCount_empty, Nat.shiftLeft_eq] at hcc
    have := Nat.two_pow_pos al; omega
  omega

end Zstd.Spec.Fse
