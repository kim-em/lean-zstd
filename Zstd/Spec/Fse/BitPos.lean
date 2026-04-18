import Zstd.Spec.Fse.Distribution

/-!
# BitPos advancement and `pos_le_size` for `decodeFseDistribution`

Proves that `decodeFseDistribution` advances `BitReader.bitPos` by at least 4
(the 4 bits read for the accuracy log) and preserves the `pos ≤ data.size`
invariant. These are prerequisites for showing the `fseCompressed` mode of
`resolveSingleFseTable` strictly advances the byte position.
-/

namespace Zstd.Spec.Fse
open ZipCommon (BitReader readBits_bitPos_eq readBits_pos_le_size)

/-! ## BitPos advancement for `decodeFseDistribution`

Proves that `decodeFseDistribution` advances `BitReader.bitPos` by at least 4,
corresponding to the 4 bits read for the accuracy log. -/

-- Helper: readBit always produces bitOff < 8
-- (The equivalent in BitReaderInvariant is private, so we reproduce it here.)
open Zstd.Native in
private theorem readBit_bitOff_lt' (br br' : BitReader) (bit : UInt32)
    (h : br.readBit = .ok (bit, br')) :
    br'.bitOff < 8 := by
  simp only [BitReader.readBit] at h
  split at h
  · exact nomatch h
  · split at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨_, rfl⟩ := h <;> dsimp only [] <;> omega

-- readBits.go preserves bitOff < 8
open Zstd.Native in
private theorem readBits_go_bitOff_lt' (br br' : BitReader)
    (acc : UInt32) (shift n : Nat) (val : UInt32)
    (h : BitReader.readBits.go br acc shift n = .ok (val, br'))
    (hbo : br.bitOff < 8) :
    br'.bitOff < 8 := by
  induction n generalizing br acc shift with
  | zero =>
    simp only [BitReader.readBits.go] at h
    obtain ⟨_, rfl⟩ := h; exact hbo
  | succ n ih =>
    simp only [BitReader.readBits.go, bind, Except.bind] at h
    cases hrb : br.readBit with
    | error e => simp only [hrb] at h; exact nomatch h
    | ok p =>
      obtain ⟨bit, br₁⟩ := p
      simp only [hrb] at h
      exact ih br₁ _ _ h (readBit_bitOff_lt' br br₁ bit hrb)

-- readBits preserves bitOff < 8
open Zstd.Native in
private theorem readBits_bitOff_lt' (br br' : BitReader) (n : Nat)
    (val : UInt32) (h : br.readBits n = .ok (val, br'))
    (hbo : br.bitOff < 8) :
    br'.bitOff < 8 :=
  readBits_go_bitOff_lt' br br' 0 0 n val h hbo

open Zstd.Native in
/-- `readProbValue` advances or preserves `bitPos` and maintains `bitOff < 8`. -/
private theorem readProbValue_bitPos_ge
    {br br' : BitReader} {remaining val : Nat}
    (h : readProbValue br remaining = .ok (val, br'))
    (hbo : br.bitOff < 8) :
    br'.bitPos ≥ br.bitPos ∧ br'.bitOff < 8 := by
  unfold readProbValue at h
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  cases hrb : br.readBits (Nat.log2 (remaining + 1) + 1 - 1) with
  | error e => rw [hrb] at h; dsimp only [Bind.bind, Except.bind] at h; exact nomatch h
  | ok val₁ =>
    rw [hrb] at h; dsimp only [Bind.bind, Except.bind] at h
    have hbp := readBits_bitPos_eq br val₁.2 _ val₁.1 hrb hbo
    have hbo₁ := readBits_bitOff_lt' br val₁.2 _ val₁.1 hrb hbo
    split at h
    · -- rawBits < lowThreshold
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨by rw [hbp]; omega, hbo₁⟩
    · -- extra bit needed
      cases hrb₂ : val₁.2.readBits 1 with
      | error e => rw [hrb₂] at h; dsimp only [Bind.bind, Except.bind] at h; exact nomatch h
      | ok val₂ =>
        rw [hrb₂] at h; dsimp only [Bind.bind, Except.bind] at h
        have hbp₂ := readBits_bitPos_eq val₁.2 val₂.2 1 val₂.1 hrb₂ hbo₁
        have hbo₂ := readBits_bitOff_lt' val₁.2 val₂.2 1 val₂.1 hrb₂ hbo₁
        split at h <;>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
          obtain ⟨_, rfl⟩ := h <;>
          exact ⟨by rw [hbp₂, hbp]; omega, hbo₂⟩

open Zstd.Native in
/-- `decodeZeroRepeats` advances or preserves `bitPos` and maintains `bitOff < 8`. -/
private theorem decodeZeroRepeats_bitPos_ge
    {br : BitReader} {probs : Array Int32} {sym ms : Nat}
    {probs' : Array Int32} {sym' : Nat} {br' : BitReader}
    (h : decodeZeroRepeats br probs sym ms = .ok (probs', sym', br'))
    (hbo : br.bitOff < 8) :
    br'.bitPos ≥ br.bitPos ∧ br'.bitOff < 8 := by
  suffices aux : ∀ (br : BitReader) (probs : Array Int32) (sym : Nat),
      ∀ {probs' : Array Int32} {sym' : Nat} {br' : BitReader},
      decodeZeroRepeats br probs sym ms = .ok (probs', sym', br') →
      br.bitOff < 8 →
      br'.bitPos ≥ br.bitPos ∧ br'.bitOff < 8 from aux _ _ _ h hbo
  intro br probs sym
  induction br, probs, sym using decodeZeroRepeats.induct (maxSymbols := ms) with
  | case1 br probs sym e hread =>
    intro _ _ _ h _
    rw [decodeZeroRepeats.eq_def, hread] at h; exact nomatch h
  | case2 br probs sym repeatBits br₁ hread repeatCount probs₁ sym₁ hpush hcnt hadv =>
    rename_i ih
    intro _ _ _ h hbo
    have hpush' : pushZeros probs sym repeatBits.toNat ms = (probs₁, sym₁) := hpush
    have hcnt' : (repeatBits.toNat == 3) = true := hcnt
    have hbp := readBits_bitPos_eq br br₁ 2 repeatBits hread hbo
    have hbo₁ := readBits_bitOff_lt' br br₁ 2 repeatBits hread hbo
    rw [decodeZeroRepeats.eq_def, hread] at h
    simp only [hpush', hcnt', ↓reduceIte, hadv, ↓reduceDIte] at h
    have ⟨hge, hbo'⟩ := ih h hbo₁
    exact ⟨by rw [hbp] at hge; omega, hbo'⟩
  | case3 br probs sym repeatBits br₁ hread repeatCount probs₁ sym₁ hpush hcnt =>
    rename_i hadv
    intro _ _ _ h _
    have hpush' : pushZeros probs sym repeatBits.toNat ms = (probs₁, sym₁) := hpush
    have hcnt' : (repeatBits.toNat == 3) = true := hcnt
    rw [decodeZeroRepeats.eq_def, hread] at h
    simp only [hcnt', ↓reduceIte, hadv, ↓reduceDIte, reduceCtorEq] at h
  | case4 br probs sym repeatBits br₁ hread repeatCount probs₁ sym₁ hpush =>
    rename_i hcnt
    intro _ _ _ h hbo
    have hpush' : pushZeros probs sym repeatBits.toNat ms = (probs₁, sym₁) := hpush
    have hcnt' : ¬((repeatBits.toNat == 3) = true) := hcnt
    have hbp := readBits_bitPos_eq br br₁ 2 repeatBits hread hbo
    have hbo₁ := readBits_bitOff_lt' br br₁ 2 repeatBits hread hbo
    rw [decodeZeroRepeats.eq_def, hread] at h
    simp only [hpush', hcnt'] at h
    obtain ⟨_, _, rfl⟩ := h
    exact ⟨by rw [hbp]; omega, hbo₁⟩

open Zstd.Native in
/-- `decodeFseLoop` preserves or advances `bitPos` and maintains `bitOff < 8`. -/
private theorem decodeFseLoop_bitPos_ge
    {br : BitReader} {rem : Nat} {probs : Array Int32}
    {sym ms : Nat} {fuel : Nat}
    {rem' : Nat} {probs' : Array Int32} {sym' : Nat} {br' : BitReader}
    (h : decodeFseLoop br rem probs sym ms fuel = .ok (rem', probs', sym', br'))
    (hbo : br.bitOff < 8) :
    br'.bitPos ≥ br.bitPos ∧ br'.bitOff < 8 := by
  induction fuel generalizing br rem probs sym with
  | zero => simp only [decodeFseLoop, reduceCtorEq] at h
  | succ fuel ih =>
    rw [decodeFseLoop.eq_2] at h
    by_cases hcond : ¬(rem > 0 ∧ sym < ms)
    · -- Loop exits: return unchanged state
      rw [if_pos hcond] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, _, rfl⟩ := h
      exact ⟨Nat.le_refl _, hbo⟩
    · -- Loop continues
      rw [if_neg hcond] at h
      cases hrpv : readProbValue br rem with
      | error e => simp only [hrpv, reduceCtorEq] at h
      | ok val =>
        simp only [hrpv] at h
        have ⟨hge_rpv, hbo_rpv⟩ := readProbValue_bitPos_ge hrpv hbo
        by_cases hp0 : (Int32.ofNat val.fst - 1 == 0) = true
        · rw [if_pos hp0] at h
          cases hzr : decodeZeroRepeats val.2 (probs.push 0) (sym + 1) ms with
          | error e => simp only [hzr, reduceCtorEq] at h
          | ok val₂ =>
            simp only [hzr] at h
            have ⟨hge_zr, hbo_zr⟩ := decodeZeroRepeats_bitPos_ge hzr hbo_rpv
            have ⟨hge_rec, hbo_rec⟩ := ih h hbo_zr
            exact ⟨by omega, hbo_rec⟩
        · rw [if_neg hp0] at h
          by_cases hp1 : (Int32.ofNat val.fst - 1 == -1) = true
          · rw [if_pos hp1] at h
            have ⟨hge_rec, hbo_rec⟩ := ih h hbo_rpv
            exact ⟨by omega, hbo_rec⟩
          · rw [if_neg hp1] at h
            by_cases hgt : int32ToNat (Int32.ofNat val.fst - 1) > rem
            · rw [if_pos hgt] at h; exact nomatch h
            · rw [if_neg hgt] at h
              have ⟨hge_rec, hbo_rec⟩ := ih h hbo_rpv
              exact ⟨by omega, hbo_rec⟩

open Zstd.Native in
/-- When `decodeFseDistribution` succeeds, the returned BitReader's `bitPos` has
    advanced by at least 4 (from the accuracy log) and `bitOff < 8` is maintained.
    Requires `bitOff < 8` (always satisfied when constructed with `bitOff := 0`
    as in the `fseCompressed` mode). -/
theorem decodeFseDistribution_bitPos_ge
    {br : BitReader} {maxSymbols maxAccLog : Nat}
    {probs : Array Int32} {al : Nat} {br' : BitReader}
    (h : decodeFseDistribution br maxSymbols maxAccLog = .ok (probs, al, br'))
    (hbo : br.bitOff < 8) :
    br'.bitPos ≥ br.bitPos + 4 ∧ br'.bitOff < 8 := by
  obtain ⟨rdval, _, hrd, _, _, hdl⟩ := decodeFseDistribution_ok_decompose h
  have hbp := readBits_bitPos_eq br rdval.2 4 rdval.1 hrd hbo
  have hbo₁ := readBits_bitOff_lt' br rdval.2 4 rdval.1 hrd hbo
  have ⟨hge_loop, hbo_loop⟩ := decodeFseLoop_bitPos_ge hdl hbo₁
  exact ⟨by rw [hbp] at hge_loop; omega, hbo_loop⟩

/-! ## BitReader pos_le_size — FSE distribution chain

These theorems establish that `readProbValue`, `decodeZeroRepeats`,
`decodeFseLoop`, and `decodeFseDistribution` preserve the invariant
`pos ≤ data.size` on success. They chain through `readBits_pos_le_size`
from `BitReaderInvariant.lean`. -/

open Zstd.Native in
/-- `readProbValue` preserves `pos ≤ data.size`. -/
theorem readProbValue_pos_le_size (br br' : BitReader) (remaining val : Nat)
    (h : readProbValue br remaining = .ok (val, br'))
    (hbr : br.pos ≤ br.data.size) :
    br'.pos ≤ br'.data.size := by
  unfold readProbValue at h
  dsimp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h
  cases hrb : br.readBits (Nat.log2 (remaining + 1) + 1 - 1) with
  | error e => rw [hrb] at h; dsimp only [Bind.bind, Except.bind] at h; exact nomatch h
  | ok val₁ =>
    rw [hrb] at h; dsimp only [Bind.bind, Except.bind] at h
    have hple₁ := readBits_pos_le_size br val₁.2 _ val₁.1 hrb hbr
    split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, rfl⟩ := h; exact hple₁
    · cases hrb₂ : val₁.2.readBits 1 with
      | error e => rw [hrb₂] at h; dsimp only [Bind.bind, Except.bind] at h; exact nomatch h
      | ok val₂ =>
        rw [hrb₂] at h; dsimp only [Bind.bind, Except.bind] at h
        have hple₂ := readBits_pos_le_size val₁.2 val₂.2 1 val₂.1 hrb₂ hple₁
        split at h <;>
          simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
          obtain ⟨_, rfl⟩ := h <;>
          exact hple₂

open Zstd.Native in
/-- `decodeZeroRepeats` preserves `pos ≤ data.size`. -/
private theorem decodeZeroRepeats_pos_le_size
    {br : BitReader} {probs : Array Int32} {sym ms : Nat}
    {probs' : Array Int32} {sym' : Nat} {br' : BitReader}
    (h : decodeZeroRepeats br probs sym ms = .ok (probs', sym', br'))
    (hbr : br.pos ≤ br.data.size) :
    br'.pos ≤ br'.data.size := by
  suffices aux : ∀ (br : BitReader) (probs : Array Int32) (sym : Nat),
      ∀ {probs' : Array Int32} {sym' : Nat} {br' : BitReader},
      decodeZeroRepeats br probs sym ms = .ok (probs', sym', br') →
      br.pos ≤ br.data.size →
      br'.pos ≤ br'.data.size from aux _ _ _ h hbr
  intro br probs sym
  induction br, probs, sym using decodeZeroRepeats.induct (maxSymbols := ms) with
  | case1 br probs sym e hread =>
    intro _ _ _ h _
    rw [decodeZeroRepeats.eq_def, hread] at h; exact nomatch h
  | case2 br probs sym repeatBits br₁ hread repeatCount probs₁ sym₁ hpush hcnt hadv =>
    rename_i ih
    intro _ _ _ h hbr
    have hpush' : pushZeros probs sym repeatBits.toNat ms = (probs₁, sym₁) := hpush
    have hcnt' : (repeatBits.toNat == 3) = true := hcnt
    have hple₁ := readBits_pos_le_size br br₁ 2 repeatBits hread hbr
    rw [decodeZeroRepeats.eq_def, hread] at h
    simp only [hpush', hcnt', ↓reduceIte, hadv, ↓reduceDIte] at h
    exact ih h hple₁
  | case3 br probs sym repeatBits br₁ hread repeatCount probs₁ sym₁ hpush hcnt =>
    rename_i hadv
    intro _ _ _ h _
    have hpush' : pushZeros probs sym repeatBits.toNat ms = (probs₁, sym₁) := hpush
    have hcnt' : (repeatBits.toNat == 3) = true := hcnt
    rw [decodeZeroRepeats.eq_def, hread] at h
    simp only [hcnt', ↓reduceIte, hadv, ↓reduceDIte, reduceCtorEq] at h
  | case4 br probs sym repeatBits br₁ hread repeatCount probs₁ sym₁ hpush =>
    rename_i hcnt
    intro _ _ _ h hbr
    have hpush' : pushZeros probs sym repeatBits.toNat ms = (probs₁, sym₁) := hpush
    have hcnt' : ¬((repeatBits.toNat == 3) = true) := hcnt
    have hple₁ := readBits_pos_le_size br br₁ 2 repeatBits hread hbr
    rw [decodeZeroRepeats.eq_def, hread] at h
    simp only [hpush', hcnt'] at h
    obtain ⟨_, _, rfl⟩ := h
    exact hple₁

open Zstd.Native in
/-- `decodeFseLoop` preserves `pos ≤ data.size`. -/
private theorem decodeFseLoop_pos_le_size
    {br : BitReader} {rem : Nat} {probs : Array Int32}
    {sym ms : Nat} {fuel : Nat}
    {rem' : Nat} {probs' : Array Int32} {sym' : Nat} {br' : BitReader}
    (h : decodeFseLoop br rem probs sym ms fuel = .ok (rem', probs', sym', br'))
    (hbr : br.pos ≤ br.data.size) :
    br'.pos ≤ br'.data.size := by
  induction fuel generalizing br rem probs sym with
  | zero => simp only [decodeFseLoop, reduceCtorEq] at h
  | succ fuel ih =>
    rw [decodeFseLoop.eq_2] at h
    by_cases hcond : ¬(rem > 0 ∧ sym < ms)
    · rw [if_pos hcond] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, _, rfl⟩ := h; exact hbr
    · rw [if_neg hcond] at h
      cases hrpv : readProbValue br rem with
      | error e => simp only [hrpv, reduceCtorEq] at h
      | ok val =>
        simp only [hrpv] at h
        have hple_rpv := readProbValue_pos_le_size br val.2 rem val.1 hrpv hbr
        by_cases hp0 : (Int32.ofNat val.fst - 1 == 0) = true
        · rw [if_pos hp0] at h
          cases hzr : decodeZeroRepeats val.2 (probs.push 0) (sym + 1) ms with
          | error e => simp only [hzr, reduceCtorEq] at h
          | ok val₂ =>
            simp only [hzr] at h
            have hple_zr := decodeZeroRepeats_pos_le_size hzr hple_rpv
            exact ih h hple_zr
        · rw [if_neg hp0] at h
          by_cases hp1 : (Int32.ofNat val.fst - 1 == -1) = true
          · rw [if_pos hp1] at h; exact ih h hple_rpv
          · rw [if_neg hp1] at h
            by_cases hgt : int32ToNat (Int32.ofNat val.fst - 1) > rem
            · rw [if_pos hgt] at h; exact nomatch h
            · rw [if_neg hgt] at h; exact ih h hple_rpv

open Zstd.Native in
/-- When `decodeFseDistribution` succeeds and the input reader has
    `pos ≤ data.size`, the output reader also has `pos ≤ data.size`. -/
theorem decodeFseDistribution_pos_le_size (br br' : BitReader)
    (maxSymbols maxAccLog : Nat) (probs : Array Int32) (al : Nat)
    (h : decodeFseDistribution br maxSymbols maxAccLog = .ok (probs, al, br'))
    (hbr : br.pos ≤ br.data.size) :
    br'.pos ≤ br'.data.size := by
  obtain ⟨rdval, _, hrd, _, _, hdl⟩ := decodeFseDistribution_ok_decompose h
  exact decodeFseLoop_pos_le_size hdl (readBits_pos_le_size br rdval.2 4 rdval.1 hrd hbr)

end Zstd.Spec.Fse
