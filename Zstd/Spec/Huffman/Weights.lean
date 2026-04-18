/-!
# Zstandard Huffman weight validity predicates (RFC 8878 §4.2.1.1)

This module defines the weight-level validity predicates used throughout
the Huffman specification:

* `weightSum` — the sum `∑ 2^(W-1)` over positive explicit weights,
* `ValidWeights` — non-empty, at least one positive weight, all ≤ 13,
* `isPow2` / `isPow2_iff` — power-of-two check used in Kraft equality,
* `KraftComplete` — the Kraft-equality constraint on `(weights, maxBits)`.

All predicates have `Decidable` instances for use with `decide`.
-/

namespace Zstd.Spec.Huffman

/-! ## Weight sum computation -/

/-- Compute the weight sum `∑ 2^(W-1)` for all positive weights in the array.
    This is the contribution of the explicitly listed symbols; the implicit
    last symbol fills the gap to `2^maxBits`. -/
def weightSum (weights : Array UInt8) : Nat :=
  weights.foldl (fun acc w =>
    if w.toNat > 0 then acc + (1 <<< (w.toNat - 1)) else acc) 0

/-! ## Weight validity predicates -/

/-- A Huffman weight array is valid when:
    (a) it is non-empty (`weights.size ≥ 1`),
    (b) at least one weight is non-zero,
    (c) no weight exceeds 13 (the practical maximum per RFC 8878 — codes
        longer than 13 bits are not useful for a 256-symbol alphabet). -/
def ValidWeights (weights : Array UInt8) : Prop :=
  weights.size ≥ 1 ∧
  (∃ i : Fin weights.size, weights[i].toNat > 0) ∧
  (∀ i : Fin weights.size, weights[i].toNat ≤ 13)

instance {weights : Array UInt8} : Decidable (ValidWeights weights) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ## Kraft completeness -/

/-- Check whether `n` is a power of 2 (i.e. `n = 2^k` for some `k`).
    Uses the standard bit-trick: `n > 0 ∧ n &&& (n - 1) = 0`. -/
def isPow2 (n : Nat) : Bool :=
  n > 0 && (n &&& (n - 1)) == 0

/-- Helper: for even n > 0, `n &&& (n - 1) = 2 * (n/2 &&& (n/2 - 1))`. -/
private theorem land_pred_even (n : Nat) (heven : n % 2 = 0) (hpos : n > 0) :
    n &&& (n - 1) = 2 * (n / 2 &&& (n / 2 - 1)) := by
  have hdiv : (n - 1) / 2 = n / 2 - 1 := by omega
  apply Nat.eq_of_testBit_eq
  intro i
  match i with
  | 0 =>
    rw [Nat.testBit_and]
    simp only [Nat.testBit_zero, heven, Nat.mul_mod_right,
      show (0 : Nat) ≠ 1 from by omega, decide_false, Bool.false_and]
  | i + 1 =>
    rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ,
        Nat.testBit_succ, Nat.mul_div_cancel_left _ (by omega : 0 < 2),
        Nat.testBit_and, hdiv]

/-- Helper: for odd n, `n &&& (n - 1) = 2 * (n / 2)`. -/
private theorem land_pred_odd (n : Nat) (hodd : n % 2 = 1) :
    n &&& (n - 1) = 2 * (n / 2) := by
  have hdiv : (n - 1) / 2 = n / 2 := by omega
  apply Nat.eq_of_testBit_eq
  intro i
  match i with
  | 0 =>
    have : (n - 1) % 2 = 0 := by omega
    rw [Nat.testBit_and]
    simp only [Nat.testBit_zero, hodd, this, Nat.mul_mod_right, decide_true, Bool.true_and]
  | i + 1 =>
    rw [Nat.testBit_and, Nat.testBit_succ, Nat.testBit_succ,
        hdiv, Bool.and_self,
        Nat.testBit_succ, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

/-- Strong induction helper: n > 0 ∧ n &&& (n-1) = 0 → ∃ k, 2^k = n. -/
private theorem land_pred_zero_imp_pow2 (n : Nat) (hpos : n > 0) (hand : n &&& (n - 1) = 0) :
    ∃ k : Nat, 2 ^ k = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
  · -- n is even: use land_pred_even to reduce to n/2
    have hge2 : n ≥ 2 := by omega
    have heven := land_pred_even n hmod hpos
    rw [hand] at heven
    -- heven : 0 = 2 * (n/2 &&& (n/2 - 1)), so n/2 &&& (n/2 - 1) = 0
    have hand2 : n / 2 &&& (n / 2 - 1) = 0 := by omega
    have ⟨j, hj⟩ := ih (n / 2) (by omega) (by omega) hand2
    exact ⟨j + 1, by rw [Nat.pow_succ, Nat.mul_comm]; omega⟩
  · -- n is odd: if n ≥ 3, then n &&& (n-1) > 0, contradiction
    -- So n must be 1
    have hodd := land_pred_odd n hmod
    rw [hand] at hodd
    -- hodd : 0 = 2 * (n / 2), so n / 2 = 0, so n = 1
    exact ⟨0, by omega⟩

/-- `isPow2` correctly characterizes powers of 2. -/
theorem isPow2_iff (n : Nat) : isPow2 n = true ↔ ∃ k : Nat, 1 <<< k = n := by
  simp only [isPow2, Nat.shiftLeft_eq, Nat.one_mul, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  constructor
  · exact fun ⟨hpos, hand⟩ => land_pred_zero_imp_pow2 n hpos hand
  · intro ⟨k, hk⟩
    subst hk
    refine ⟨Nat.two_pow_pos k, ?_⟩
    -- 2^k &&& (2^k - 1) = 0 by induction using land_pred_even
    induction k with
    | zero => decide
    | succ k ih =>
      have hdiv : 2 ^ (k + 1) / 2 = 2 ^ k := by
        rw [Nat.pow_succ, Nat.mul_comm, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
      rw [land_pred_even (2 ^ (k + 1))
        (by rw [Nat.pow_succ, Nat.mul_comm]; exact Nat.mul_mod_right 2 _)
        (Nat.two_pow_pos _), hdiv, ih]

/-- The Kraft equality holds for `weights` and `maxBits` when the sum of
    `2^(W-1)` for all positive explicit weights, plus the implicit last
    symbol's contribution, equals exactly `2^maxBits`.  Equivalently:
    `weightSum weights < 2^maxBits` (the implicit symbol fills the gap),
    and the gap is itself a power of 2.

    This is the fundamental constraint from RFC 8878 §4.2.1.1: the total
    must be a complete prefix-free code. -/
def KraftComplete (weights : Array UInt8) (maxBits : Nat) : Prop :=
  let ws := weightSum weights
  ws > 0 ∧
  ws < 1 <<< maxBits ∧
  isPow2 ((1 <<< maxBits) - ws) = true

instance {weights : Array UInt8} {maxBits : Nat} :
    Decidable (KraftComplete weights maxBits) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end Zstd.Spec.Huffman
