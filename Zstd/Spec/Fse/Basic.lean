import Zstd.Native.Fse
import ZipCommon.BitReader
import ZipCommon.Spec.BitReaderInvariant

/-!
# FSE Distribution and Table Validity Predicates

Formal specification of FSE (Finite State Entropy) distribution validity
and table structure for Zstandard compressed blocks (RFC 8878 §4.1).

This module defines predicates characterizing:
- `ValidAccuracyLog`: accuracy log in the range [5, 9] per RFC 8878 §4.1
- `ValidDistribution`: probability distribution satisfying RFC constraints
- `ValidFseTable`: structural invariants of a decoded FSE table

These predicates formalize the validity checks performed by
`Zstd.Native.decodeFseDistribution` and the structural properties
guaranteed by `Zstd.Native.buildFseTable`. All predicates have `Decidable`
instances for use with `decide`.
-/

namespace Zstd.Spec.Fse

open Zstd.Native (FseCell)
open ZipCommon (BitReader)

/-- The accuracy log for an FSE table is valid per RFC 8878 §4.1 when it
    falls in the range [5, 9]. This is the range for sequence-level FSE
    tables (literal lengths, match lengths, offsets). Huffman weight tables
    use a wider range but this captures the common case. -/
def ValidAccuracyLog (al : Nat) : Prop :=
  5 ≤ al ∧ al ≤ 9

instance {al : Nat} : Decidable (ValidAccuracyLog al) :=
  inferInstanceAs (Decidable (5 ≤ al ∧ al ≤ 9))

/-- Compute the total cell count from a probability distribution.
    Positive probabilities contribute their value; -1 probabilities
    (indicating "less than 1") each contribute 1 cell. Zero entries
    contribute nothing. This matches the counting logic in
    `decodeFseDistribution` where `remaining` starts at `1 << accuracyLog`
    and is decremented by each positive probability or by 1 for each
    -1 probability. -/
def cellCount (dist : Array Int32) : Nat :=
  dist.foldl (fun acc p =>
    if p.toInt > 0 then acc + p.toInt.toNat
    else if p == -1 then acc + 1
    else acc) 0

/-- A probability distribution is valid for a given accuracy log when:
    (a) all probabilities are ≥ -1,
    (b) the total cell count (positive probs summed + count of -1 entries)
        equals the table size `1 << accuracyLog`, and
    (c) at least one symbol has positive probability. -/
def ValidDistribution (dist : Array Int32) (accuracyLog : Nat) : Prop :=
  (∀ i : Fin dist.size, dist[i].toInt ≥ -1) ∧
  cellCount dist = 1 <<< accuracyLog ∧
  (∃ i : Fin dist.size, dist[i].toInt > 0)

instance {dist : Array Int32} {accuracyLog : Nat} :
    Decidable (ValidDistribution dist accuracyLog) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- An FSE decoding table satisfies structural invariants when:
    (a) its size equals `1 << accuracyLog`,
    (b) all symbol indices are less than `numSymbols`, and
    (c) all `numBits` values are at most `accuracyLog`. -/
def ValidFseTable (table : Array FseCell) (accuracyLog : Nat)
    (numSymbols : Nat) : Prop :=
  table.size = 1 <<< accuracyLog ∧
  (∀ i : Fin table.size, table[i].symbol.toNat < numSymbols) ∧
  (∀ i : Fin table.size, table[i].numBits.toNat ≤ accuracyLog)

instance {table : Array FseCell} {accuracyLog numSymbols : Nat} :
    Decidable (ValidFseTable table accuracyLog numSymbols) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ## cellCount helper lemmas -/

/-- cellCount of a push reduces to a single if-then-else. -/
theorem cellCount_push (dist : Array Int32) (p : Int32) :
    cellCount (dist.push p) =
      if p.toInt > 0 then cellCount dist + p.toInt.toNat
      else if p == -1 then cellCount dist + 1
      else cellCount dist := by
  simp only [cellCount, gt_iff_lt, Int32.toNat_toInt, beq_iff_eq, Array.size_push,
    Array.foldl_push']

@[simp] theorem cellCount_push_zero (dist : Array Int32) :
    cellCount (dist.push 0) = cellCount dist := by
  rw [cellCount_push]
  simp only [show ¬((0 : Int32).toInt > 0) from by decide,
    show ((0 : Int32) == -1) = false from by decide, ↓reduceIte, Bool.false_eq_true]

@[simp] theorem cellCount_empty : cellCount #[] = 0 := by
  simp only [cellCount, List.foldl_toArray', List.foldl_nil]

/-! ## Generic `Except` helper

This helper decomposes a successful monadic bind; it is shared between
`BuildTable` and `Predefined` submodules. -/

/-- If `x >>= f = .ok b`, then `x` succeeded and `f` maps its result to `.ok b`. -/
theorem Except.bind_eq_ok' {α β ε : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = Except.ok b) : ∃ a, x = Except.ok a ∧ f a = Except.ok b := by
  cases x with
  | error e => simp only [bind, Except.bind, reduceCtorEq] at h
  | ok a => exact ⟨a, rfl, h⟩

/-! ## Loop invariant lemmas for decodeFseDistribution -/

open Zstd.Native in
/-- Pushing zeros preserves `cellCount`. -/
theorem pushZeros_cellCount (probs : Array Int32) (sym n ms : Nat) :
    cellCount (pushZeros probs sym n ms).1 = cellCount probs := by
  induction n generalizing probs sym with
  | zero => rfl
  | succ n ih =>
    unfold pushZeros
    split
    · rw [ih]; exact cellCount_push_zero probs
    · rfl

open Zstd.Native in
/-- The zero-repeat inner loop only pushes zeros, so `cellCount` is preserved. -/
theorem decodeZeroRepeats_cellCount
    {br : BitReader} {probs : Array Int32} {sym ms : Nat}
    {probs' : Array Int32} {sym' : Nat} {br' : BitReader}
    (h : decodeZeroRepeats br probs sym ms = .ok (probs', sym', br')) :
    cellCount probs' = cellCount probs := by
  suffices aux : ∀ (br : BitReader) (probs : Array Int32) (sym : Nat),
      ∀ {probs' : Array Int32} {sym' : Nat} {br' : BitReader},
      decodeZeroRepeats br probs sym ms = .ok (probs', sym', br') →
      cellCount probs' = cellCount probs from aux _ _ _ h
  intro br probs sym
  induction br, probs, sym using decodeZeroRepeats.induct (maxSymbols := ms) with
  | case1 br probs sym e hread =>
    intro _ _ _ h; rw [decodeZeroRepeats.eq_def, hread] at h; exact nomatch h
  | case2 br probs sym repeatBits br₁ hread repeatCount probs₁ sym₁ hpush hcnt hadv =>
    rename_i ih
    intro _ _ _ h
    have hpush' : pushZeros probs sym repeatBits.toNat ms = (probs₁, sym₁) := hpush
    have hcnt' : (repeatBits.toNat == 3) = true := hcnt
    rw [decodeZeroRepeats.eq_def, hread] at h
    simp only [hpush', hcnt', ↓reduceIte, hadv, ↓reduceDIte] at h
    have hpc : cellCount probs₁ = cellCount probs := by
      have := pushZeros_cellCount probs sym repeatBits.toNat ms
      rw [hpush'] at this; exact this
    rw [ih h, hpc]
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
    rw [decodeZeroRepeats.eq_def, hread] at h
    simp only [hpush', hcnt'] at h
    obtain ⟨rfl, _, _⟩ := h
    have := pushZeros_cellCount probs sym repeatBits.toNat ms
    rw [hpush'] at this; exact this

open Zstd.Native in
/-- Main loop invariant: `remaining + cellCount probs` is preserved across
    all iterations of `decodeFseLoop`. -/
theorem decodeFseLoop_invariant
    {br : BitReader} {rem : Nat} {probs : Array Int32}
    {sym ms : Nat}
    {rem' : Nat} {probs' : Array Int32} {sym' : Nat} {br' : BitReader}
    (h : decodeFseLoop br rem probs sym ms = .ok (rem', probs', sym', br')) :
    rem' + cellCount probs' = rem + cellCount probs := by
  suffices aux : ∀ (br : BitReader) (rem : Nat) (probs : Array Int32) (sym : Nat),
      ∀ {rem' : Nat} {probs' : Array Int32} {sym' : Nat} {br' : BitReader},
      decodeFseLoop br rem probs sym ms = .ok (rem', probs', sym', br') →
      rem' + cellCount probs' = rem + cellCount probs from aux _ _ _ _ h
  intro br rem probs sym
  induction br, rem, probs, sym using decodeFseLoop.induct (maxSymbols := ms) with
  | case1 br rem probs sym hrun e hrpv =>
    intro _ _ _ _ h
    rw [decodeFseLoop.eq_def, dif_pos hrun, hrpv] at h; exact nomatch h
  | case2 br rem probs sym hrun val br₁ hrpv _prob hp0 e =>
    rename_i hzr
    intro _ _ _ _ h
    have hp0 : (Int32.ofNat val - 1 == 0) = true := hp0
    have hzr : decodeZeroRepeats br₁ (probs.push 0) (sym + 1) ms = .error e := hzr
    rw [decodeFseLoop.eq_def, dif_pos hrun, hrpv] at h
    simp only [hp0, ↓reduceIte, hzr] at h; exact nomatch h
  | case3 br rem probs sym hrun val br₁ hrpv _prob hp0 probs₁ sym₁ br₂ hzr hadv =>
    rename_i ih
    intro _ _ _ _ h
    have hp0 : (Int32.ofNat val - 1 == 0) = true := hp0
    rw [decodeFseLoop.eq_def, dif_pos hrun, hrpv] at h
    simp only [hp0, ↓reduceIte, hzr, hadv, ↓reduceDIte] at h
    rw [ih h, decodeZeroRepeats_cellCount hzr, cellCount_push_zero]
  | case4 br rem probs sym hrun val br₁ hrpv _prob hp0 probs₁ sym₁ br₂ hzr =>
    rename_i hadv
    intro _ _ _ _ h
    have hp0 : (Int32.ofNat val - 1 == 0) = true := hp0
    rw [decodeFseLoop.eq_def, dif_pos hrun, hrpv] at h
    simp only [hp0, ↓reduceIte, hzr, hadv, ↓reduceDIte] at h; exact nomatch h
  | case5 br rem probs sym hrun val br₁ hrpv _prob hp0 hp1 =>
    rename_i ih
    intro _ _ _ _ h
    have hp0' : ¬(Int32.ofNat val - 1 == 0) = true := hp0
    have hp1' : (Int32.ofNat val - 1 == -1) = true := hp1
    rw [decodeFseLoop.eq_def, dif_pos hrun, hrpv] at h
    simp only [hp0', ↓reduceIte, hp1'] at h
    rw [ih h, cellCount_push, eq_of_beq hp1]
    simp only [show ((-1 : Int32).toInt > 0) = False from by decide,
                show ((-1 : Int32) == -1) = true from by decide,
                ↓reduceIte]
    omega
  | case6 br rem probs sym hrun val br₁ hrpv _prob hp0 hp1 =>
    rename_i hgt
    intro _ _ _ _ h
    have hp0 : ¬(Int32.ofNat val - 1 == 0) = true := hp0
    have hp1 : ¬(Int32.ofNat val - 1 == -1) = true := hp1
    have hgt : int32ToNat (Int32.ofNat val - 1) > rem := hgt
    rw [decodeFseLoop.eq_def, dif_pos hrun, hrpv] at h
    simp only [hp0, ↓reduceIte, hp1, hgt] at h; exact nomatch h
  | case7 br rem probs sym hrun val br₁ hrpv _prob hp0 hp1 =>
    rename_i _probNat hgt ih
    intro _ _ _ _ h
    have hp0' : ¬(Int32.ofNat val - 1 == 0) = true := hp0
    have hp1' : ¬(Int32.ofNat val - 1 == -1) = true := hp1
    have hgt' : ¬int32ToNat (Int32.ofNat val - 1) > rem := hgt
    rw [decodeFseLoop.eq_def, dif_pos hrun, hrpv] at h
    simp only [hp0', ↓reduceIte, hp1', hgt'] at h
    rw [ih h, cellCount_push]
    by_cases hpos : _prob.toInt > 0
    · rw [if_pos hpos]
      change ¬int32ToNat _prob > rem at hgt
      change rem - int32ToNat _prob + (cellCount probs + _prob.toInt.toNat) = rem + cellCount probs
      simp only [int32ToNat, show ¬_prob.toInt < 0 from by omega, ↓reduceIte] at hgt ⊢
      omega
    · rw [if_neg hpos, if_neg hp1]
      change rem - int32ToNat _prob + cellCount probs = rem + cellCount probs
      simp only [int32ToNat]
      split <;> omega
  | case8 br rem probs sym hrun =>
    intro _ _ _ _ h
    rw [decodeFseLoop.eq_def, dif_neg hrun] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, _, _⟩ := h; rfl

end Zstd.Spec.Fse
