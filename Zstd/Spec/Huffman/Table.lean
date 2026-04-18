import Zstd.Native.Huffman
import Zstd.Spec.Huffman.Weights

/-!
# Zstandard Huffman table validity and `buildZstdHuffmanTable` correctness

This module defines the `ValidHuffmanTable` structural invariant on flat
Huffman decoding tables, proves the correctness theorems for the
`buildZstdHuffmanTable` function (size, `maxBits ≥ 1`, `numBits ≤ maxBits`,
and the composite `_valid` statement), and relates the inline weight-sum
loop to the extensional `weightSum` function.

A handful of concrete `decide`-powered examples exercise the predicates
on small weight arrays.
-/

namespace Zstd.Spec.Huffman

open Zstd.Native (HuffmanEntry ZstdHuffmanTable)

/-! ## Table validity predicates -/

/-- A flat Huffman decoding table satisfies structural invariants when:
    (a) `table.size = 1 << maxBits` (the table is fully populated),
    (b) all entries have `numBits ≤ maxBits`, and
    (c) all symbol indices are at most 255 (fit in UInt8, always true
        by construction but useful for downstream reasoning). -/
def ValidHuffmanTable (table : Array HuffmanEntry) (maxBits : Nat) : Prop :=
  table.size = 1 <<< maxBits ∧
  (∀ i : Fin table.size, table[i].numBits.toNat ≤ maxBits) ∧
  (∀ i : Fin table.size, table[i].symbol.toNat ≤ 255)

instance {table : Array HuffmanEntry} {maxBits : Nat} :
    Decidable (ValidHuffmanTable table maxBits) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ## Helper: forIn with pure yield reduces to foldl -/

/-- When the body of `forIn` over an `Array` in the `Except` monad always
    returns `Except.ok (ForInStep.yield ...)`, the result equals `Except.ok`
    of the corresponding `Array.foldl`.

    This is proved by converting through `Array.forIn_eq_foldlM` and
    `Array.foldlM_toList`, then inducting on `as.toList`. -/
private theorem forIn_pure_yield_eq_foldl {ε : Type} (as : Array α) (f : α → β → β) (init : β) :
    forIn as init (fun a b =>
      (Except.ok (ForInStep.yield (f a b)) : Except ε (ForInStep β))) =
    (Except.ok (as.foldl (fun b a => f a b) init) : Except ε β) := by
  rw [Array.forIn_eq_foldlM, ← Array.foldlM_toList, ← Array.foldl_toList]
  generalize as.toList = l
  revert init
  induction l with
  | nil => intro init; rfl
  | cons x l ih =>
    intro init
    simp only [List.foldlM, bind, Except.bind, List.foldl_cons]
    exact ih (f x init)

/-! ## Correctness theorems -/

open Zstd.Native in
/-- The WF loop always returns at least its initial `maxBits` argument. -/
private theorem findMaxBitsWF_ge (ws maxBits power : Nat) (hp : power > 0) :
    findMaxBitsWF ws maxBits power hp ≥ maxBits := by
  unfold findMaxBitsWF
  split
  · have ih := findMaxBitsWF_ge ws (maxBits + 1) (power * 2) (by omega); omega
  · split <;> omega
termination_by ws - power

open Zstd.Native in
/-- When `weightSum ≥ 1`, `findMaxBitsWF weightSum 0 1 _ ≥ 1`. -/
private theorem findMaxBitsWF_ge_one (ws : Nat) (hws : ws ≥ 1) :
    findMaxBitsWF ws 0 1 (by omega) ≥ 1 := by
  unfold findMaxBitsWF
  split
  · -- 1 < ws: recurse with maxBits=1, power=2
    exact Nat.le_trans (by omega : 1 ≤ 1) (findMaxBitsWF_ge ws 1 2 (by omega))
  · -- ¬(1 < ws), so ws ≤ 1, combined with ws ≥ 1 means ws = 1
    split <;> simp only [beq_iff_eq] at * <;> omega

open Zstd.Native in
/-- When `weightsToMaxBits` succeeds, the result is at least 1.  The weight sum
    is ≥ 1 (the guard rejects zero), and `findMaxBitsWF` with initial power = 1
    always returns ≥ 1 when the weight sum is positive. -/
private theorem weightsToMaxBits_ge_one (weights : Array UInt8) (m : Nat)
    (h : weightsToMaxBits weights = .ok m) : m ≥ 1 := by
  simp only [weightsToMaxBits, bind, Except.bind] at h
  -- Layer 1: forIn weights (weightSum accumulation loop)
  split at h
  · exact nomatch h
  · rename_i ws _
    -- Layer 2: guard (weightSum == 0)
    split at h
    · exact nomatch h
    · -- guard passes, pure () reduces
      dsimp only [pure, Pure.pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      exact findMaxBitsWF_ge_one ws (by simp only [beq_iff_eq] at *; omega)

open Zstd.Native in
/-- The WF loop returns a value `m` such that `ws ≤ 2^m`, given the loop
    invariant `power = 2^maxBits`. -/
private theorem findMaxBitsWF_bound (ws maxBits power : Nat) (hp : power > 0)
    (hinv : power = 1 <<< maxBits) :
    ws ≤ 1 <<< (findMaxBitsWF ws maxBits power hp) := by
  unfold findMaxBitsWF
  split
  · -- power < ws: recurse with doubled power
    exact findMaxBitsWF_bound ws (maxBits + 1) (power * 2) (by omega)
      (by simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_succ] at hinv ⊢; omega)
  · split
    · -- ws == power: return maxBits + 1
      rename_i _ h2; simp only [beq_iff_eq] at h2; subst h2
      simp only [hinv, Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_succ]
      have := Nat.two_pow_pos maxBits; omega
    · -- power ≥ ws: return maxBits
      rename_i h1 _
      have := Nat.le_of_not_lt h1; rw [hinv] at this; exact this
termination_by ws - power

open Zstd.Native in
/-- The inner fill loop preserves array size: each step either uses `set!`
    (which preserves size) or leaves the table unchanged. -/
private theorem fillHuffmanTableInnerWF_preserves_size
    (table : Array HuffmanEntry) (entry : HuffmanEntry)
    (code stride sym lastSymbol j : Nat)
    (result : Array HuffmanEntry)
    (h : fillHuffmanTableInnerWF table entry code stride sym lastSymbol j = .ok result) :
    result.size = table.size := by
  unfold fillHuffmanTableInnerWF at h
  split at h
  · -- j ≥ stride: result = table
    simp only [Except.ok.injEq] at h; subst h; rfl
  · -- j < stride: reduce `have idx := ...`
    dsimp only [] at h
    split at h
    · -- idx < table.size: recurse with table.set
      have ih := fillHuffmanTableInnerWF_preserves_size _ entry code stride
        sym lastSymbol (j + 1) result h
      rw [ih, Array.size_set]
    · -- idx ≥ table.size
      split at h
      · exact nomatch h  -- throw: contradiction
      · -- skip: recurse with table unchanged
        exact fillHuffmanTableInnerWF_preserves_size _ entry code stride
          sym lastSymbol (j + 1) result h
termination_by stride - j

open Zstd.Native in
/-- The outer fill loop preserves array size. -/
private theorem fillHuffmanTableWF_preserves_size
    (table : Array HuffmanEntry) (allWeights : Array UInt8)
    (nextCode : Array Nat) (maxBits numSymbols lastSymbol sym : Nat)
    (haw : numSymbols ≤ allWeights.size)
    (resultTable : Array HuffmanEntry) (resultNextCode : Array Nat)
    (h : fillHuffmanTableWF table allWeights nextCode maxBits
      numSymbols lastSymbol sym haw = .ok (resultTable, resultNextCode)) :
    resultTable.size = table.size := by
  unfold fillHuffmanTableWF at h
  split at h
  · -- sym ≥ numSymbols: result = table
    simp only [Except.ok.injEq, Prod.mk.injEq] at h; rw [h.1]
  · -- sym < numSymbols: reduce `have w := ...`
    dsimp only [] at h
    split at h
    · -- w == 0: recurse unchanged
      exact fillHuffmanTableWF_preserves_size _ allWeights nextCode maxBits
        numSymbols lastSymbol (sym + 1) haw resultTable resultNextCode h
    · -- w ≠ 0: split on guard
      split at h
      · -- w < nextCode.size: split on inner match
        split at h
        · -- inner succeeded with table'
          rename_i _ _ _ hinner
          have hsize := fillHuffmanTableInnerWF_preserves_size _ _ _ _ _ _ _ _ hinner
          have ih := fillHuffmanTableWF_preserves_size _ allWeights _ maxBits
            numSymbols lastSymbol _ haw resultTable resultNextCode h
          rw [ih, hsize]
        · exact nomatch h  -- inner threw
      · exact nomatch h  -- w ≥ nextCode.size: threw
termination_by numSymbols - sym

/-- Decompose a successful `buildZstdHuffmanTable` call: `weightsToMaxBits` succeeded
    with `result.maxBits`, and the table has size `1 <<< result.maxBits`.  This peels
    through the 7 monadic layers of the do-block once, deduplicating the shared work
    between `buildZstdHuffmanTable_tableSize` and `buildZstdHuffmanTable_maxBits_pos`. -/
private theorem buildZstdHuffmanTable_ok_elim (weights : Array UInt8)
    (result : ZstdHuffmanTable)
    (h : Zstd.Native.buildZstdHuffmanTable weights = .ok result) :
    Zstd.Native.weightsToMaxBits weights = .ok result.maxBits ∧
    result.table.size = 1 <<< result.maxBits := by
  open Zstd.Native in
  simp only [buildZstdHuffmanTable, bind, Except.bind] at h
  cases hwm : weightsToMaxBits weights with
  | error e => simp only [hwm] at h; exact nomatch h
  | ok m =>
    rw [hwm] at h; dsimp only [Bind.bind, Except.bind] at h
    -- Peel through 7 monadic layers (forIn, guard, while, guard, weightCounts, nextCode, fill)
    split at h; · exact nomatch h
    · split at h; · exact nomatch h
      · dsimp only [pure, Pure.pure, Except.pure] at h
        split at h; · exact nomatch h
        · split at h; · exact nomatch h
          · split at h; · exact nomatch h
            · split at h; · exact nomatch h
              · split at h
                · exact nomatch h
                · rename_i _ v hfill
                  simp only [Except.ok.injEq] at h
                  constructor
                  · rw [← h]
                  · subst h
                    obtain ⟨filledTable, filledNextCode⟩ := v
                    simp only at hfill ⊢
                    have hpres := fillHuffmanTableWF_preserves_size _ _ _ _ _ _ _ _ _ _ hfill
                    rw [hpres, Array.size_replicate]

/-- When `buildZstdHuffmanTable` succeeds, the resulting table has size `1 <<< maxBits`. -/
theorem buildZstdHuffmanTable_tableSize (weights : Array UInt8)
    (result : ZstdHuffmanTable)
    (h : Zstd.Native.buildZstdHuffmanTable weights = .ok result) :
    result.table.size = 1 <<< result.maxBits :=
  (buildZstdHuffmanTable_ok_elim weights result h).2

/-- When `buildZstdHuffmanTable` succeeds, `maxBits ≥ 1`. -/
theorem buildZstdHuffmanTable_maxBits_pos (weights : Array UInt8)
    (result : ZstdHuffmanTable)
    (h : Zstd.Native.buildZstdHuffmanTable weights = .ok result) :
    result.maxBits ≥ 1 :=
  weightsToMaxBits_ge_one weights result.maxBits (buildZstdHuffmanTable_ok_elim weights result h).1

open Zstd.Native in
/-- `Array.set` preserves a pointwise property on `HuffmanEntry` arrays:
    if all entries satisfy `P` and the new value satisfies `P`, then all
    entries of the updated array satisfy `P`. -/
private theorem huffman_set_preserves_forall {P : HuffmanEntry → Prop}
    {table : Array HuffmanEntry} {idx : Nat} {v : HuffmanEntry}
    {hidx : idx < table.size}
    (hall : ∀ j : Fin table.size, P table[j])
    (hv : P v) :
    ∀ j : Fin (table.set idx v hidx).size, P (table.set idx v hidx)[j] := by
  intro ⟨j, hj⟩
  simp only [Array.size_set] at hj
  by_cases hij : idx = j
  · subst hij; exact Array.getElem_set_self hidx ▸ hv
  · exact (Array.getElem_set_ne hidx hj hij) ▸ hall ⟨j, hj⟩

open Zstd.Native in
/-- The inner fill loop preserves the `numBits ≤ maxBits` invariant.
    Each step either writes an entry with `numBits = (maxBits + 1 - w).toUInt8`
    (where `w ≥ 1`, so `numBits.toNat ≤ maxBits`) or leaves the table unchanged. -/
private theorem fillHuffmanTableInnerWF_numBits_le
    (table : Array HuffmanEntry) (entry : HuffmanEntry)
    (code stride sym lastSymbol j : Nat)
    (result : Array HuffmanEntry) (maxBits : Nat)
    (hentry : entry.numBits.toNat ≤ maxBits)
    (hinv : ∀ i : Fin table.size, table[i].numBits.toNat ≤ maxBits)
    (h : fillHuffmanTableInnerWF table entry code stride sym lastSymbol j = .ok result) :
    ∀ i : Fin result.size, result[i].numBits.toNat ≤ maxBits := by
  unfold fillHuffmanTableInnerWF at h
  split at h
  · -- j ≥ stride: result = table
    simp only [Except.ok.injEq] at h; subst h; exact hinv
  · -- j < stride
    dsimp only [] at h
    split at h
    · -- idx < table.size: recurse with table.set
      exact fillHuffmanTableInnerWF_numBits_le _ entry code stride
        sym lastSymbol (j + 1) result maxBits hentry
        (huffman_set_preserves_forall (P := fun e => e.numBits.toNat ≤ maxBits) hinv hentry) h
    · split at h
      · exact nomatch h  -- throw: contradiction
      · -- skip: recurse with table unchanged
        exact fillHuffmanTableInnerWF_numBits_le _ entry code stride
          sym lastSymbol (j + 1) result maxBits hentry hinv h
termination_by stride - j

open Zstd.Native in
/-- The outer fill loop preserves the `numBits ≤ maxBits` invariant.
    For each symbol with weight `w > 0`, the entry has `numBits = (maxBits + 1 - w).toUInt8`.
    Since `w ≥ 1`, `(maxBits + 1 - w) ≤ maxBits`, so `numBits.toNat ≤ maxBits`. -/
private theorem fillHuffmanTableWF_numBits_le
    (table : Array HuffmanEntry) (allWeights : Array UInt8)
    (nextCode : Array Nat) (maxBits numSymbols lastSymbol sym : Nat)
    (haw : numSymbols ≤ allWeights.size)
    (resultTable : Array HuffmanEntry) (resultNextCode : Array Nat)
    (hinv : ∀ i : Fin table.size, table[i].numBits.toNat ≤ maxBits)
    (h : fillHuffmanTableWF table allWeights nextCode maxBits
      numSymbols lastSymbol sym haw = .ok (resultTable, resultNextCode)) :
    ∀ i : Fin resultTable.size, resultTable[i].numBits.toNat ≤ maxBits := by
  unfold fillHuffmanTableWF at h
  split at h
  · -- sym ≥ numSymbols: result = table
    simp only [Except.ok.injEq, Prod.mk.injEq] at h; rw [h.1] at hinv; exact hinv
  · -- sym < numSymbols
    dsimp only [] at h
    split at h
    · -- w == 0: recurse unchanged
      exact fillHuffmanTableWF_numBits_le _ allWeights nextCode maxBits
        numSymbols lastSymbol (sym + 1) haw resultTable resultNextCode hinv h
    · -- w ≠ 0
      rename_i hw0
      split at h
      · -- w < nextCode.size: inner loop then recurse
        split at h
        · -- inner succeeded
          rename_i _ _ hinner
          have hw_pos : (allWeights[sym]'(by omega)).toNat ≥ 1 := by
            revert hw0; simp only [beq_iff_eq]; omega
          have hentry : ({ symbol := sym.toUInt8,
                           numBits := (maxBits + 1 - (allWeights[sym]'(by omega)).toNat).toUInt8 }
                         : HuffmanEntry).numBits.toNat ≤ maxBits := by
            simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
            have hmod : (maxBits + 1 - (allWeights[sym]'(by omega)).toNat) % 2 ^ 8 ≤
                    maxBits + 1 - (allWeights[sym]'(by omega)).toNat := Nat.mod_le _ _
            omega
          have hinv' := fillHuffmanTableInnerWF_numBits_le _ _ _ _ _ _ _ _
            maxBits hentry hinv hinner
          exact fillHuffmanTableWF_numBits_le _ allWeights _ maxBits
            numSymbols lastSymbol _ haw resultTable resultNextCode hinv' h
        · exact nomatch h  -- inner threw
      · exact nomatch h  -- w ≥ nextCode.size: threw
termination_by numSymbols - sym

open Zstd.Native in
/-- When `buildZstdHuffmanTable` succeeds, every table entry's `numBits`
    is at most `maxBits`. This threads the invariant through the initial
    `Array.replicate` (default `numBits = 0`), the `fillHuffmanTableWF`
    outer loop, and its `fillHuffmanTableInnerWF` inner loop. -/
theorem buildZstdHuffmanTable_numBits_le (weights : Array UInt8)
    (result : ZstdHuffmanTable)
    (h : Zstd.Native.buildZstdHuffmanTable weights = .ok result)
    (i : Fin result.table.size) :
    result.table[i].numBits.toNat ≤ result.maxBits := by
  -- Decompose the buildZstdHuffmanTable call
  simp only [buildZstdHuffmanTable, bind, Except.bind] at h
  cases hwm : weightsToMaxBits weights with
  | error e => simp only [hwm] at h; exact nomatch h
  | ok m =>
    rw [hwm] at h; dsimp only [Bind.bind, Except.bind] at h
    split at h; · exact nomatch h
    · split at h; · exact nomatch h
      · dsimp only [pure, Pure.pure, Except.pure] at h
        split at h; · exact nomatch h
        · split at h; · exact nomatch h
          · split at h; · exact nomatch h
            · split at h; · exact nomatch h
              · split at h
                · exact nomatch h
                · rename_i _ v hfill
                  obtain ⟨filledTable, filledNextCode⟩ := v
                  simp only [Except.ok.injEq] at h; subst h
                  -- Initial table: Array.replicate with default has numBits = 0
                  have hinit : ∀ j : Fin (Array.replicate (1 <<< m) (default : HuffmanEntry)).size,
                      (Array.replicate (1 <<< m) (default : HuffmanEntry))[j].numBits.toNat ≤ m := by
                    intro ⟨j, hj⟩
                    show (Array.replicate (1 <<< m) (default : HuffmanEntry))[j].numBits.toNat ≤ m
                    rw [Array.getElem_replicate]; exact Nat.zero_le _
                  exact (fillHuffmanTableWF_numBits_le _ _ _ m _ _ _ _ _ _ hinit hfill) i

open Zstd.Native in
/-- When `buildZstdHuffmanTable` succeeds, the resulting table satisfies
    `ValidHuffmanTable`: size equals `1 <<< maxBits`, all `numBits` values
    are at most `maxBits`, and all symbol indices are at most 255.

    This composes `buildZstdHuffmanTable_tableSize`,
    `buildZstdHuffmanTable_numBits_le`, and the trivial `UInt8` bound. -/
theorem buildZstdHuffmanTable_valid (weights : Array UInt8)
    (result : ZstdHuffmanTable)
    (h : Zstd.Native.buildZstdHuffmanTable weights = .ok result) :
    ValidHuffmanTable result.table result.maxBits :=
  ⟨buildZstdHuffmanTable_tableSize weights result h,
   fun i => buildZstdHuffmanTable_numBits_le weights result h i,
   fun i => Nat.lt_succ_iff.mp (UInt8.toNat_lt result.table[i].symbol)⟩

/-- When `weightsToMaxBits` succeeds with result `m`, the weight sum
    satisfies `0 < weightSum ≤ 2^m`. The function finds the smallest
    `k` with `2^k ≥ weightSum`, then bumps by 1 if equality holds
    (to accommodate the implicit last symbol).

    The original statement claimed `weightSum ≤ 2^(m-1)`, which is false:
    e.g. `weights = #[1, 2]` gives `weightSum = 3`, `m = 2`, but
    `3 > 2^(2-1) = 2`. The correct bound is `2^m`. -/
theorem weightsToMaxBits_valid (weights : Array UInt8)
    (m : Nat)
    (h : Zstd.Native.weightsToMaxBits weights = .ok m) :
    weightSum weights > 0 ∧ weightSum weights ≤ 1 <<< m := by
  open Zstd.Native in
  simp only [weightsToMaxBits, bind, Except.bind] at h
  split at h
  · exact nomatch h
  · rename_i ws heq_forIn
    split at h
    · exact nomatch h
    · dsimp only [pure, Pure.pure, Except.pure] at h
      simp only [Except.ok.injEq] at h
      subst h
      have hws : ws = weightSum weights := by
        -- Simplify match on pure PUnit.unit (do-notation desugaring artifact)
        simp only [pure, Pure.pure, Except.pure] at heq_forIn
        -- Pull Except.ok (ForInStep.yield ...) out of the if branches
        simp only [show ∀ (w : UInt8) (r : Nat),
            (if w.toNat > 0 then (Except.ok (ForInStep.yield (r + 1 <<< (w.toNat - 1))))
             else (Except.ok (ForInStep.yield r) : Except String (ForInStep Nat))) =
            Except.ok (ForInStep.yield (if w.toNat > 0 then r + 1 <<< (w.toNat - 1) else r))
          from fun w r => by split <;> rfl] at heq_forIn
        rw [forIn_pure_yield_eq_foldl] at heq_forIn
        exact (Except.ok.inj heq_forIn).symm
      rw [← hws]
      exact ⟨by simp only [beq_iff_eq] at *; omega,
             findMaxBitsWF_bound ws 0 1 (by omega) rfl⟩

/-- The `weightSum` function agrees with the inline computation in
    `weightsToMaxBits`: both compute `∑ 2^(W-1)` for positive weights. -/
theorem weightSum_eq_inline (weights : Array UInt8) :
    weightSum weights =
      weights.foldl (fun acc w =>
        if w.toNat > 0 then acc + (1 <<< (w.toNat - 1)) else acc) 0 := by
  rfl

/-- The weight fold step never decreases the accumulator. -/
private theorem weightStep_ge (acc : Nat) (w : UInt8) :
    acc ≤ (if w.toNat > 0 then acc + (1 <<< (w.toNat - 1)) else acc) := by
  split
  · exact Nat.le_add_right acc _
  · exact Nat.le_refl acc

/-- The weight fold over a list preserves a lower bound on the accumulator. -/
private theorem weightFold_ge_init (l : List UInt8) (acc : Nat) :
    acc ≤ l.foldl (fun acc w =>
      if w.toNat > 0 then acc + (1 <<< (w.toNat - 1)) else acc) acc := by
  induction l generalizing acc with
  | nil => exact Nat.le_refl _
  | cons x l ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (weightStep_ge acc x) (ih _)

/-- A single non-zero weight gives a non-zero weight sum. -/
theorem weightSum_pos_of_exists_nonzero (weights : Array UInt8)
    (i : Fin weights.size) (hi : weights[i].toNat > 0) :
    weightSum weights > 0 := by
  unfold weightSum
  rw [← Array.foldl_toList]
  -- Split the list at index i
  rw [show weights.toList = weights.toList.take i.val ++ weights.toList.drop i.val
        from (List.take_append_drop i.val weights.toList).symm,
      List.foldl_append,
      show weights.toList.drop i.val =
        weights.toList[i.val] :: weights.toList.drop (i.val + 1)
        from List.drop_eq_getElem_cons (by simp only [Array.length_toList]; exact i.isLt),
      List.foldl_cons]
  -- After processing weights[i], the accumulator is ≥ 1
  apply Nat.lt_of_lt_of_le Nat.zero_lt_one
  apply Nat.le_trans _ (weightFold_ge_init _ _)
  split
  · -- 1 <<< k ≥ 1, so acc + (1 <<< k) ≥ 1
    exact Nat.le_trans
      (show 1 ≤ 1 <<< (weights.toList[↑i].toNat - 1) by
        simp only [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.two_pow_pos _)
      (Nat.le_add_left _ _)
  · -- Contradiction: weights.toList[↑i] = weights[i], whose toNat > 0
    next hc => exact absurd (by simpa only [Array.getElem_toList] using hi) hc

/-! ## Concrete validation examples -/

/-- The empty weight array has zero weight sum. -/
theorem weightSum_empty : weightSum #[] = 0 := by decide

/-- A single weight of 1 gives weight sum 1 (= 2^0). -/
theorem weightSum_singleton : weightSum #[1] = 1 := by decide

/-- Two weights of 1 gives weight sum 2 (= 1 + 1). -/
theorem weightSum_two_ones : weightSum #[1, 1] = 2 := by decide

/-- The weights `#[1, 1]` are valid: non-empty, at least one positive,
    all ≤ 13. -/
theorem validWeights_two_ones : ValidWeights #[1, 1] := by decide

/-- The weights `#[1, 1]` satisfy Kraft completeness with `maxBits = 2`:
    `weightSum = 2`, `2^2 = 4`, gap = 2 which is a power of 2. -/
theorem kraft_two_ones : KraftComplete #[1, 1] 2 := by decide

/-- A weight of 2 contributes 2 (= 2^1) to the sum. -/
theorem weightSum_weight2 : weightSum #[2] = 2 := by decide

/-- The weights `#[2, 1]` satisfy Kraft completeness with `maxBits = 2`:
    `weightSum = 2 + 1 = 3`, `2^2 = 4`, gap = 1 which is a power of 2. -/
theorem kraft_mixed : KraftComplete #[2, 1] 2 := by decide

end Zstd.Spec.Huffman
