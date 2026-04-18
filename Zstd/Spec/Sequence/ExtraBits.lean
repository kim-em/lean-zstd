import Zstd.Native.Sequence

/-!
# Extra-bits table correctness (RFC 8878 Tables 14–15)

Size and value characterizations for the three per-sequence decoders:
literal-length, match-length, and offset. Covers the identity-mapping
small-code ranges, the match-length minimum of 3, and the offset
positivity/ge-two lemmas used downstream.
-/

namespace Zstd.Spec.Sequence

open Zstd.Native (litLenExtraBits matchLenExtraBits decodeLitLenValue decodeMatchLenValue
  decodeOffsetValue)

/-! ## Extra bits table correctness (RFC 8878 Tables 14–15) -/

/-- The literal length extra bits table has exactly 36 entries (codes 0–35, RFC 8878 Table 14). -/
theorem litLenExtraBits_size : litLenExtraBits.size = 36 := by rfl

/-- The match length extra bits table has exactly 53 entries (codes 0–52, RFC 8878 Table 15). -/
theorem matchLenExtraBits_size : matchLenExtraBits.size = 53 := by rfl

/-- For literal length codes 0–15, the decoded value equals `code + extraBits`
    (baseline equals code, zero extra bits in the table). This validates that
    the first 16 entries of RFC 8878 Table 14 are identity mappings. -/
theorem decodeLitLenValue_small (code : Nat) (extraBits : UInt32) (h : code ≤ 15) :
    decodeLitLenValue code extraBits = .ok (code + extraBits.toNat) := by
  have hlt : code < litLenExtraBits.size := by simp only [litLenExtraBits_size]; omega
  unfold decodeLitLenValue
  simp only [hlt, ↓reduceDIte]
  rcases code with _ | _ | _ | _ | _ | _ | _ | _ |
                   _ | _ | _ | _ | _ | _ | _ | _ | _
  all_goals first | omega | rfl

/-- For match length codes 0–31, the decoded value equals `code + 3 + extraBits`
    (baseline equals code + 3, zero extra bits in the table). This validates that
    the first 32 entries of RFC 8878 Table 15 are offset-by-3 identity mappings. -/
theorem decodeMatchLenValue_small (code : Nat) (extraBits : UInt32) (h : code ≤ 31) :
    decodeMatchLenValue code extraBits = .ok (code + 3 + extraBits.toNat) := by
  have hlt : code < matchLenExtraBits.size := by simp only [matchLenExtraBits_size]; omega
  unfold decodeMatchLenValue
  simp only [hlt, ↓reduceDIte]
  rcases code with _ | _ | _ | _ | _ | _ | _ | _ |
                   _ | _ | _ | _ | _ | _ | _ | _ |
                   _ | _ | _ | _ | _ | _ | _ | _ |
                   _ | _ | _ | _ | _ | _ | _ | _ | _
  all_goals first | omega | rfl

/-- Any successful match length decoding produces a value ≥ 3.
    This is the Zstd minimum match length (RFC 8878 §3.1.1.3.2.1.2):
    every entry in `matchLenExtraBits` has baseline ≥ 3, and the decoded
    value is `baseline + extraBits.toNat`. -/
private theorem matchLen_baselines_ge_three_aux :
    ∀ i : Fin matchLenExtraBits.size, (matchLenExtraBits[i.val]'i.isLt).1 ≥ 3 := by
  set_option cbv.warning false in
    decide_cbv

private theorem matchLen_baselines_ge_three (i : Nat) (hi : i < matchLenExtraBits.size) :
    (matchLenExtraBits[i]'hi).1 ≥ 3 :=
  matchLen_baselines_ge_three_aux ⟨i, hi⟩

theorem decodeMatchLenValue_ge_three (code : Nat) (extraBits : UInt32) (n : Nat)
    (h : decodeMatchLenValue code extraBits = .ok n) :
    n ≥ 3 := by
  unfold decodeMatchLenValue at h
  split at h
  · rename_i hlt
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact Nat.le_trans (matchLen_baselines_ge_three code hlt) (Nat.le_add_right _ _)
  · exact nomatch h

/-- `decodeOffsetValue` always returns a positive value.
    This follows from `(1 <<< code) ≥ 1` for any natural `code`. -/
theorem decodeOffsetValue_positive (code : Nat) (extraBits : UInt32) :
    decodeOffsetValue code extraBits > 0 := by
  unfold decodeOffsetValue
  have : 1 <<< code ≥ 1 := by rw [Nat.one_shiftLeft]; exact Nat.one_le_two_pow
  omega

/-- When `code ≥ 1`, `decodeOffsetValue` returns a value ≥ 2.
    This distinguishes non-repeat offsets (≥ 2) from repeat offsets (code 0).
    Follows from `1 <<< code = 2^code ≥ 2` when `code ≥ 1`. -/
theorem decodeOffsetValue_ge_two (code : Nat) (extraBits : UInt32) (hcode : code ≥ 1) :
    decodeOffsetValue code extraBits ≥ 2 := by
  unfold decodeOffsetValue
  have : 1 <<< code ≥ 2 := by
    rw [Nat.one_shiftLeft]
    cases code with
    | zero => omega
    | succ n => rw [Nat.pow_succ]; have := Nat.one_le_two_pow (n := n); omega
  omega

end Zstd.Spec.Sequence
