import Zstd.Spec.Fse.Basic

/-!
# Structural properties of `buildFseTable`

Threads the main `buildFseTable` invariants through its four bind-chained
loops:
- `accuracyLog_eq`, `cells_size`, `numBits_le`
- always-succeeds: `buildFseTable_ok`
- `newState_lt`, `symbol_lt`, and the composed `ValidFseTable` witness
-/

namespace Zstd.Spec.Fse

open Zstd.Native (FseCell)

/-! ## Structural properties of `buildFseTable` -/

/-- `List.forIn'.loop` in `Except` preserves a predicate when the body preserves it
    on both `.yield` and `.done` outcomes. Error outcomes are handled by the hypothesis
    that the overall loop succeeded. The body must ignore the membership proof. -/
private theorem forIn'_loop_preserves {α β ε : Type}
    (P : β → Prop) (as curr : List α) (init result : β)
    (f : α → β → Except ε (ForInStep β))
    (h_init : P init)
    (h_yield : ∀ a b b', P b → f a b = .ok (.yield b') → P b')
    (h_done : ∀ a b b', P b → f a b = .ok (.done b') → P b')
    (hsuf : ∃ bs, bs ++ curr = as)
    (h_result : List.forIn'.loop as (fun a _ b => f a b) curr init hsuf = .ok result) :
    P result := by
  induction curr generalizing init with
  | nil =>
    unfold List.forIn'.loop at h_result
    dsimp only [pure, Except.pure] at h_result
    rw [← Except.ok.inj h_result]; exact h_init
  | cons x xs ih =>
    unfold List.forIn'.loop at h_result
    dsimp only [Bind.bind, Except.bind] at h_result
    cases hfx : f x init with
    | error e => rw [hfx] at h_result; exact nomatch h_result
    | ok step =>
      rw [hfx] at h_result
      cases step with
      | done b' =>
        dsimp only [pure, Except.pure] at h_result
        rw [← Except.ok.inj h_result]; exact h_done x init b' h_init hfx
      | yield b' =>
        exact ih b' (h_yield x init b' h_init hfx) _ h_result

open Zstd.Native in
/-- When `buildFseTable` succeeds, the returned accuracy log equals the input.
    This follows from the return statement `{ accuracyLog, cells }` where
    `accuracyLog` is the input parameter unchanged. -/
theorem buildFseTable_accuracyLog_eq (probs : Array Int32) (al : Nat)
    (table : FseTable) (h : buildFseTable probs al = .ok table) :
    table.accuracyLog = al := by
  simp only [buildFseTable, bind, Except.bind, pure, Except.pure] at h
  -- grind handles case-splitting through the unfolded if/match/forIn branches,
  -- extracting `table.accuracyLog = al` from each successful return path
  grind

private theorem forIn_range_preserves {β ε : Type}
    (P : β → Prop) (n : Nat) (init result : β)
    (f : Nat → β → Except ε (ForInStep β))
    (h_init : P init)
    (h_yield : ∀ a b b', P b → f a b = .ok (.yield b') → P b')
    (h_done : ∀ a b b', P b → f a b = .ok (.done b') → P b')
    (h_result : forIn [:n] init f = .ok result) :
    P result := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h_result
  exact forIn'_loop_preserves P _ _ init result f h_init h_yield h_done _ h_result

open Zstd.Native in
/-- When `buildFseTable` succeeds, the returned cells array has size `1 <<< al`.
    This follows from `Array.replicate` setting the initial size and `Array.set!`
    preserving size through all loop iterations. -/
theorem buildFseTable_cells_size (probs : Array Int32) (al : Nat)
    (table : FseTable) (h : buildFseTable probs al = .ok table) :
    table.cells.size = 1 <<< al := by
  simp only [buildFseTable] at h
  -- Decompose the do-notation bind chain into individual loop equations
  obtain ⟨v1, hloop1, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v2, hloop2, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v3, hloop3, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v4, hloop4, h⟩ := Except.bind_eq_ok' h
  simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  -- Thread cells size invariant: replicate → loop1 → loop2 → loop4
  -- (loop3 only modifies symbolCounts, not cells)
  -- Loop 1 (place -1 probability symbols): cells.set! preserves size
  have hsize1 : v1.fst.size = 1 <<< al := by
    apply forIn_range_preserves (fun s => s.fst.size = 1 <<< al) _ _ _ _ _ _ _ hloop1
    · exact Array.size_replicate
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · split at heq
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]
          simp only [Nat.toUInt16_eq, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hb]
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> exact nomatch heq
  -- Loop 2 (distribute symbols with stepping): cells.set! preserves size
  have hsize2 : v2.fst.size = 1 <<< al := by
    apply forIn_range_preserves (fun s => s.fst.size = 1 <<< al) _ _ _ _ _ _ _ hloop2
    · exact hsize1
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · -- if h_sym : sym < probs.size
        split at heq
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
        · -- Inner forIn with while loop
          split at heq
          · exact nomatch heq
          · rename_i r hinner
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
            apply forIn_range_preserves (fun s => s.fst.size = 1 <<< al) _ _ _ _ _ _ _ hinner
            · exact hb
            · intro a2 b2 b2' hb2 heq2
              rw [← ForInStep.yield.inj (Except.ok.inj heq2)]
              simp only [Nat.toUInt16_eq, Array.set!_eq_setIfInBounds,
                Array.size_setIfInBounds, hb2]
            · intro a2 b2 b2' hb2 heq2
              exact nomatch heq2
      · -- h_sym doesn't hold
        rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · intro _ _ _ _ heq; simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> (try split at heq) <;> exact nomatch heq
  -- Loop 4 (compute numBits/newState): cells.set! preserves size
  apply forIn_range_preserves (fun s => s.fst.size = 1 <<< al) _ _ _ _ _ _ _ hloop4
  · exact hsize2
  · intro a b b' hb heq
    simp only [bind, Except.bind, pure, Except.pure] at heq
    split at heq
    · -- if h_i : i < cells.size
      split at heq
      · -- if h_sc : sym < symbolCounts.size
        split at heq
        · -- if h_si : sym < symbolStateIndex.size
          split at heq
          · -- if count != 0
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]
            simp only [Nat.toUInt8_eq, Nat.toUInt16_eq, Array.set!_eq_setIfInBounds,
              Array.size_setIfInBounds, hb]
          · -- count == 0
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · -- h_i doesn't hold
      rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
  · intro _ _ _ _ heq; simp only [bind, Except.bind, pure, Except.pure] at heq
    split at heq <;> (try split at heq) <;> (try split at heq) <;>
    (try split at heq) <;> exact nomatch heq

/-- `Array.set!` preserves a Fin-indexed property when the new value satisfies it.
    After `set!`, each cell is either the new value (at the written index) or
    unchanged from the original array. -/
private theorem set!_preserves_forall {P : FseCell → Prop}
    {cells : Array FseCell} {idx : Nat} {v : FseCell}
    (hall : ∀ j : Fin cells.size, P cells[j])
    (hv : P v) :
    ∀ j : Fin (cells.set! idx v).size, P (cells.set! idx v)[j] := by
  intro ⟨j, hj⟩
  simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] at hj
  show P (cells.setIfInBounds idx v)[j]
  by_cases hij : idx = j
  · subst hij
    exact (Array.getElem_setIfInBounds_self (h := by
      simp only [Array.size_setIfInBounds]; exact hj)) ▸ hv
  · exact (Array.getElem_setIfInBounds_ne hj hij) ▸ hall ⟨j, hj⟩

open Zstd.Native in
/-- When `buildFseTable` succeeds, every cell's `numBits` is at most `al`.
    This follows from the construction: loops 1-2 set cells with default
    `numBits = 0`, loop 3 doesn't modify cells, and loop 4 sets
    `numBits := (al - Nat.log2 nextState).toUInt8` where `al - x ≤ al`. -/
theorem buildFseTable_numBits_le (probs : Array Int32) (al : Nat)
    (table : FseTable) (h : buildFseTable probs al = .ok table)
    (i : Fin table.cells.size) :
    table.cells[i].numBits.toNat ≤ al := by
  simp only [buildFseTable] at h
  obtain ⟨v1, hloop1, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v2, hloop2, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v3, hloop3, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v4, hloop4, h⟩ := Except.bind_eq_ok' h
  simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  show v4.fst[i].numBits.toNat ≤ al
  -- The predicate P: cell.numBits.toNat ≤ al
  let P : FseCell → Prop := fun c => c.numBits.toNat ≤ al
  -- Initial cells: Array.replicate with default has numBits = 0
  have hinit : ∀ j : Fin (Array.replicate (1 <<< al) (default : FseCell)).size,
      P (Array.replicate (1 <<< al) (default : FseCell))[j] := by
    intro ⟨j, hj⟩; show P _
    simp only [Fin.getElem_fin, Array.getElem_replicate]; exact Nat.zero_le _
  -- Loop 1: preserves property (sets cells with { symbol := ... }, default numBits = 0)
  have h1 : ∀ j : Fin v1.fst.size, P v1.fst[j] := by
    apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, P s.fst[j])
      _ _ _ _ hinit _ _ hloop1
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · split at heq
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
          exact set!_preserves_forall hb (show P _ from Nat.zero_le _)
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> exact nomatch heq
  -- Loop 2: preserves property (sets cells with { symbol := ... }, default numBits = 0)
  have h2 : ∀ j : Fin v2.fst.size, P v2.fst[j] := by
    apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, P s.fst[j])
      _ _ _ _ h1 _ _ hloop2
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · split at heq
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
        · split at heq
          · exact nomatch heq
          · rename_i r hinner
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
            apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, P s.fst[j])
              _ _ _ _ hb _ _ hinner
            · intro a2 b2 b2' hb2 heq2
              rw [← ForInStep.yield.inj (Except.ok.inj heq2)]; dsimp only
              exact set!_preserves_forall hb2 (show P _ from Nat.zero_le _)
            · intro a2 b2 b2' hb2 heq2; exact nomatch heq2
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · intro _ _ _ _ heq; simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> (try split at heq) <;> exact nomatch heq
  -- Loop 3 modifies only symbolCounts (v3 : Array Nat), not cells.
  -- Loop 4 starts with v2.fst as its initial cells.
  -- Loop 4: sets numBits := (al - Nat.log2 nextState).toUInt8
  -- The key bound: (al - x).toUInt8.toNat ≤ al
  have numBits_bound : ∀ x : Nat, (al - x).toUInt8.toNat ≤ al := by
    intro x
    simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
    exact Nat.le_trans (Nat.mod_le _ _) (Nat.sub_le al x)
  apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, P s.fst[j])
    _ _ _ _ h2 _ _ hloop4
  · intro a b b' hb heq
    simp only [bind, Except.bind, pure, Except.pure] at heq
    split at heq
    · -- if h_i : i < cells.size
      split at heq
      · -- if h_sc
        split at heq
        · -- if h_si
          split at heq
          · -- count != 0: set! with numBits bound
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
            exact set!_preserves_forall hb (numBits_bound _)
          · -- count == 0
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
  · intro _ _ _ _ heq; simp only [bind, Except.bind, pure, Except.pure] at heq
    split at heq <;> (try split at heq) <;> (try split at heq) <;>
    (try split at heq) <;> exact nomatch heq

/-! ## forIn always-ok lemmas -/

/-- `List.forIn'.loop` in `Except` always returns `.ok` when the body never throws. -/
private theorem forIn'_loop_always_ok {α β ε : Type}
    (as curr : List α) (init : β)
    (f : α → β → Except ε (ForInStep β))
    (h_ok : ∀ a b, ∃ r, f a b = .ok r)
    (hsuf : ∃ bs, bs ++ curr = as) :
    ∃ result, List.forIn'.loop as (fun a _ b => f a b) curr init hsuf = .ok result := by
  induction curr generalizing init with
  | nil =>
    unfold List.forIn'.loop
    exact ⟨init, rfl⟩
  | cons x xs ih =>
    unfold List.forIn'.loop
    dsimp only [Bind.bind, Except.bind]
    obtain ⟨r, hr⟩ := h_ok x init
    rw [hr]
    cases r with
    | done b' => exact ⟨b', rfl⟩
    | yield b' => exact ih b' _

/-- `forIn` over a range in `Except` always returns `.ok` when the body never throws. -/
private theorem forIn_range_always_ok {β ε : Type} (n : Nat) (init : β)
    (f : Nat → β → Except ε (ForInStep β))
    (h_ok : ∀ i b, ∃ r, f i b = .ok r) :
    ∃ result, forIn [:n] init f = .ok result := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact forIn'_loop_always_ok _ _ init (fun a b => f a b) h_ok _

/-! ## buildFseTable always succeeds -/

/-- If `x` always returns `.ok` and `f` always returns `.ok`, then `x >>= f`
    always returns `.ok`. -/
private theorem Except.bind_always_ok {α β ε : Type} {x : Except ε α}
    {f : α → Except ε β}
    (hx : ∃ a, x = .ok a) (hf : ∀ a, ∃ b, f a = .ok b) :
    ∃ b, (x >>= f) = .ok b := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hf a
  exact ⟨b, by rw [ha]; exact hb⟩

open Zstd.Native in
/-- `buildFseTable` always succeeds — its body contains only pure array
    operations (set!, replicate, arithmetic) and never throws. -/
theorem buildFseTable_ok (probs : Array Int32) (al : Nat) :
    ∃ table, buildFseTable probs al = .ok table := by
  simp only [buildFseTable]
  -- The goal is a chain of binds over 4 forIn loops, ending with pure.
  -- Each loop body only returns .ok (.yield _), so each loop succeeds.
  apply Except.bind_always_ok
  · -- Loop 1: all branches return .ok (.yield _)
    exact forIn_range_always_ok _ _ _ (fun i b => by
      simp only [bind, Except.bind, pure, Except.pure]
      split <;> (try split) <;> exact ⟨_, rfl⟩)
  · intro v1
    apply Except.bind_always_ok
    · -- Loop 2: distribute symbols (body contains nested forIn)
      exact forIn_range_always_ok _ _ _ (fun i b => by
        simp only [bind, Except.bind, pure, Except.pure]
        split
        · -- if h_sym
          split
          · exact ⟨_, rfl⟩
          · -- Nested forIn inside a bind chain
            apply Except.bind_always_ok
            · exact forIn_range_always_ok _ _ _
                (fun j c => ⟨_, rfl⟩)
            · intro r; exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩)
    · intro v2
      apply Except.bind_always_ok
      · -- Loop 3: count symbols
        exact forIn_range_always_ok _ _ _ (fun i b => by
          simp only [bind, Except.bind, pure, Except.pure]
          split <;> (try split) <;> exact ⟨_, rfl⟩)
      · intro v3
        apply Except.bind_always_ok
        · -- Loop 4: compute numBits/newState
          exact forIn_range_always_ok _ _ _ (fun i b => by
            simp only [bind, Except.bind, pure, Except.pure]
            split <;> (try split) <;> (try split) <;> (try split) <;> exact ⟨_, rfl⟩)
        · intro v4
          exact ⟨_, rfl⟩

/-! ## Helper lemmas for newState bound -/

/-- `Nat.log2 n ≤ k` when `n < 2^(k+1)`. Inverse of `Nat.lt_log2_self`. -/
private theorem log2_le_of_lt_pow2_succ (n k : Nat) (h : n < 2 ^ (k + 1)) :
    Nat.log2 n ≤ k := by
  if hle : Nat.log2 n ≤ k then exact hle else
  exfalso
  have h3 : n ≠ 0 := by intro heq; subst heq; simp at hle
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h
    (Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) (Nat.log2_self_le h3)))

/-- `n * 2^(k - log2 n) < 2^(k+1)` when `log2 n ≤ k`. This bounds the
    shifted value `nextState <<< numBits` in FSE table construction. -/
private theorem mul_pow_sub_log2_lt (n k : Nat) (hk : Nat.log2 n ≤ k) :
    n * 2 ^ (k - Nat.log2 n) < 2 ^ (k + 1) :=
  calc n * 2 ^ (k - Nat.log2 n)
      < 2 ^ (Nat.log2 n + 1) * 2 ^ (k - Nat.log2 n) :=
        (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr Nat.lt_log2_self
    _ = 2 ^ (k + 1) := by rw [← Nat.pow_add]; congr 1; omega

/-- The baseline value `(nextState <<< numBits) - tableSize`, converted to
    UInt16, is less than `1 <<< al` when `nextState < 2 * (1 <<< al)`. -/
private theorem baseline_toUInt16_lt (nextState al : Nat)
    (hlt : nextState < 2 * (1 <<< al)) :
    ((nextState <<< (al - Nat.log2 nextState)) - (1 <<< al)).toUInt16.toNat <
      1 <<< al := by
  simp only [Nat.shiftLeft_eq, Nat.one_mul] at *
  have hlog : Nat.log2 nextState ≤ al :=
    log2_le_of_lt_pow2_succ _ _ (by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ al)]; exact hlt)
  have hmul := mul_pow_sub_log2_lt nextState al hlog
  -- hmul : nextState * 2^(al - log2 nextState) < 2^(al+1)
  -- Rewrite 2^(al+1) = 2 * 2^al, keeping LHS unchanged
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ al)] at hmul
  -- Now hmul : nextState * 2^numBits < 2 * 2^al, both sides normalized
  simp only [Nat.toUInt16_eq, UInt16.toNat_ofNat']
  omega

/-- `Array.getD` after `set!`: the result is `v` for the modified index (if in bounds),
    or the original `getD` otherwise. -/
private theorem getD_set! (a : Array Nat) (i v s : Nat) :
    (a.set! i v).getD s 0 = if i = s ∧ i < a.size then v else a.getD s 0 := by
  simp only [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  split <;> split <;> grind

private theorem getD_eq_getElem (a : Array Nat) (i : Nat) (h : i < a.size) :
    a.getD i 0 = a[i] := by
  unfold Array.getD; exact dif_pos h

/-! ## Indexed loop invariant -/

/-- `List.forIn'.loop` in `Except` preserves an index-dependent predicate.
    The index `offset` tracks how many elements have been processed so far.
    This is stronger than `forIn'_loop_preserves` when the predicate needs
    to grow with the iteration count (e.g., bounding accumulated values). -/
private theorem forIn'_loop_preserves_indexed {α β ε : Type}
    (P : Nat → β → Prop) (target : Nat)
    (as curr : List α) (init result : β)
    (f : α → β → Except ε (ForInStep β))
    (offset : Nat)
    (h_init : P offset init)
    (h_yield : ∀ (k : Nat) (a : α) (b b' : β),
      k < target → P k b → f a b = .ok (.yield b') → P (k + 1) b')
    (h_done : ∀ (k : Nat) (a : α) (b b' : β),
      P k b → f a b = .ok (.done b') → P target b')
    (hsuf : ∃ bs, bs ++ curr = as)
    (h_len : offset + curr.length = target)
    (h_result : List.forIn'.loop as (fun a _ b => f a b) curr init hsuf =
      .ok result) :
    P target result := by
  induction curr generalizing init offset with
  | nil =>
    unfold List.forIn'.loop at h_result
    dsimp only [pure, Except.pure] at h_result
    rw [← Except.ok.inj h_result]
    simp only [List.length_nil, Nat.add_zero] at h_len
    exact h_len ▸ h_init
  | cons x xs ih =>
    unfold List.forIn'.loop at h_result
    dsimp only [Bind.bind, Except.bind] at h_result
    cases hfx : f x init with
    | error e => rw [hfx] at h_result; exact nomatch h_result
    | ok step =>
      rw [hfx] at h_result
      cases step with
      | done b' =>
        dsimp only [pure, Except.pure] at h_result
        rw [← Except.ok.inj h_result]
        exact h_done offset x init b' h_init hfx
      | yield b' =>
        have hlt : offset < target := by
          simp only [List.length_cons] at h_len; omega
        exact ih b' (offset + 1)
          (h_yield offset x init b' hlt h_init hfx) _
          (by simp only [List.length_cons] at h_len; omega) h_result

/-- `forIn` over a range `[:n]` preserves an index-dependent predicate `P k b`
    where `k` tracks the iteration count from 0 to n. -/
private theorem forIn_range_preserves_indexed {β ε : Type}
    (P : Nat → β → Prop) (n : Nat) (init result : β)
    (f : Nat → β → Except ε (ForInStep β))
    (h_init : P 0 init)
    (h_yield : ∀ (k : Nat) (a : Nat) (b b' : β),
      k < n → P k b → f a b = .ok (.yield b') → P (k + 1) b')
    (h_done : ∀ (k : Nat) (a : Nat) (b b' : β),
      P k b → f a b = .ok (.done b') → P n b')
    (h_result : forIn [:n] init f = .ok result) :
    P n result := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h_result
  exact forIn'_loop_preserves_indexed P n _ _ init result f 0
    h_init h_yield h_done _
    (by simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one,
      List.length_range', Nat.zero_add])
    h_result

/-! ## buildFseTable newState bound -/

open Zstd.Native in
/-- When `buildFseTable` succeeds, every cell's `newState` is less than
    `1 <<< al` (the table size). This ensures the FSE state machine stays
    in bounds: the next state `newState + readBits(numBits)` lands within
    the table.

    The proof tracks two invariants:
    - Loop 3 (counting): each `symbolCounts[sym] ≤ tableSize` (via indexed
      loop invariant — each count ≤ iteration index ≤ tableSize)
    - Loop 4 (assignment): each `symbolStateIndex[sym] ≤ iteration index`,
      so `stateIdx < tableSize`. Combined with `count ≤ tableSize`, this
      gives `nextState = count + stateIdx < 2 * tableSize`, enabling the
      algebraic bound on `baseline.toUInt16`. -/
theorem buildFseTable_newState_lt (probs : Array Int32) (al : Nat)
    (table : FseTable) (h : buildFseTable probs al = .ok table)
    (i : Fin table.cells.size) :
    table.cells[i].newState.toNat < 1 <<< al := by
  simp only [buildFseTable] at h
  obtain ⟨v1, hloop1, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v2, hloop2, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v3, hloop3, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v4, hloop4, h⟩ := Except.bind_eq_ok' h
  simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  show v4.fst[i].newState.toNat < 1 <<< al
  -- Establish type aliases for clarity
  -- v3 : Array Nat (symbolCounts)
  -- v4 : Array FseCell × Array Nat (cells × symbolStateIndex)
  -- The per-cell predicate
  let Q : FseCell → Prop := fun c => c.newState.toNat < 1 <<< al
  -- The default cell has newState = 0 < tableSize
  have hQ_default : Q default := by
    change (0 : UInt16).toNat < 1 <<< al
    simp only [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.two_pow_pos _
  -- Initial cells: Array.replicate with default has newState = 0
  have hinit : ∀ j : Fin (Array.replicate (1 <<< al) (default : FseCell)).size,
      Q (Array.replicate (1 <<< al) (default : FseCell))[j] := by
    intro ⟨j, hj⟩
    simp only [Fin.getElem_fin, Array.getElem_replicate]; exact hQ_default
  -- Loop 1: preserves Q (sets cells with { symbol := ... }, default newState = 0)
  have h1 : ∀ j : Fin v1.fst.size, Q v1.fst[j] := by
    apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, Q s.fst[j])
      _ _ _ _ hinit _ _ hloop1
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · split at heq
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
          exact set!_preserves_forall hb hQ_default
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> exact nomatch heq
  -- Loop 2: preserves Q (sets cells with { symbol := ... }, default newState = 0)
  have h2 : ∀ j : Fin v2.fst.size, Q v2.fst[j] := by
    apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, Q s.fst[j])
      _ _ _ _ h1 _ _ hloop2
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · split at heq
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
        · split at heq
          · exact nomatch heq
          · rename_i r hinner
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
            apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, Q s.fst[j])
              _ _ _ _ hb _ _ hinner
            · intro a2 b2 b2' hb2 heq2
              rw [← ForInStep.yield.inj (Except.ok.inj heq2)]; dsimp only
              exact set!_preserves_forall hb2 hQ_default
            · intro a2 b2 b2' hb2 heq2; exact nomatch heq2
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · intro _ _ _ _ heq; simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> (try split at heq) <;> exact nomatch heq
  -- Loop 3 (counting): prove each symbolCounts[sym] ≤ tableSize
  -- Use indexed invariant: after k iterations, each count ≤ k
  have h3_counts : ∀ s, v3.getD s 0 ≤ 1 <<< al := by
    apply forIn_range_preserves_indexed
      (fun k (sc : Array Nat) => ∀ s, sc.getD s 0 ≤ k)
      _ _ _ _ _ _ _ hloop3
    · -- Initial: Array.replicate probs.size 0, all zeros ≤ 0
      intro s; unfold Array.getD; split
        <;> simp only [Array.getInternal_eq_getElem, Array.getElem_replicate, Std.le_refl]
    · -- Yield step: incrementing one element preserves bound
      intro k _ b b' _ hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · -- if h_i : i < cells.size
        split at heq
        · -- if h_sym : sym < symbolCounts.size — set! sym (count + 1)
          rw [← ForInStep.yield.inj (Except.ok.inj heq)]
          intro s; rw [getD_set!]; split
          · -- modified index: count + 1 ≤ k + 1
            rename_i h; obtain ⟨rfl, h_lt⟩ := h
            rw [← getD_eq_getElem _ _ h_lt]
            exact Nat.succ_le_succ (hb _)
          · -- other index: old value ≤ k ≤ k + 1
            exact Nat.le_succ_of_le (hb s)
        · -- h_sym doesn't hold: no change
          rw [← ForInStep.yield.inj (Except.ok.inj heq)]
          intro s; exact Nat.le_succ_of_le (hb s)
      · -- h_i doesn't hold: no change
        rw [← ForInStep.yield.inj (Except.ok.inj heq)]
        intro s; exact Nat.le_succ_of_le (hb s)
    · -- Done: never happens (body always yields)
      intro k _ b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> exact nomatch heq
  -- Loop 4: compute numBits/newState for each cell
  -- Use indexed invariant: symIdx values ≤ iteration count
  -- Combined with h3_counts (count ≤ tableSize) and the algebraic bound
  have h4 : (∀ j : Fin v4.fst.size, Q v4.fst[j]) ∧
      (∀ sym, v4.snd.getD sym 0 ≤ 1 <<< al) := by
    apply forIn_range_preserves_indexed
      (P := fun k s =>
        (∀ j : Fin s.fst.size, Q s.fst[j]) ∧ (∀ sym, s.snd.getD sym 0 ≤ k))
      (h_init := ⟨h2, fun sym => by
        unfold Array.getD; split
          <;> simp only [Array.getInternal_eq_getElem, Array.getElem_replicate, Std.le_refl]⟩)
      (h_result := hloop4)
    · -- Yield step
      intro k kv b b' hk ⟨hcells, hsymIdx⟩ heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · -- if h_i : i < cells.size
        split at heq
        · -- if h_sc : sym < symbolCounts.size
          split at heq
          · -- if h_si : sym < symbolStateIndex.size
            split at heq
            · -- count != 0: Main case
              rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
              refine ⟨?_, ?_⟩
              · -- Cells property: set! preserves Q, new value satisfies Q
                apply set!_preserves_forall hcells
                show Q _; unfold Q; dsimp only []
                apply baseline_toUInt16_lt
                -- Convert getD to getElem using the in-bounds proofs from the if-guards
                have hcount := h3_counts (b.fst[kv].symbol.toNat)
                rw [getD_eq_getElem _ _ ‹b.fst[kv].symbol.toNat < v3.size›] at hcount
                have hstateIdx := hsymIdx (b.fst[kv].symbol.toNat)
                rw [getD_eq_getElem _ _ ‹b.fst[kv].symbol.toNat < b.snd.size›] at hstateIdx
                omega
              · -- symIdx property: set! sym (stateIdx + 1) preserves getD ≤ k + 1
                intro s; rw [getD_set!]; split
                · rename_i h; obtain ⟨rfl, h_lt⟩ := h
                  rw [← getD_eq_getElem _ _ h_lt]
                  exact Nat.succ_le_succ (hsymIdx _)
                · exact Nat.le_succ_of_le (hsymIdx s)
            · -- count == 0
              rw [← ForInStep.yield.inj (Except.ok.inj heq)]
              exact ⟨hcells, fun sym => Nat.le_succ_of_le (hsymIdx sym)⟩
          · rw [← ForInStep.yield.inj (Except.ok.inj heq)]
            exact ⟨hcells, fun sym => Nat.le_succ_of_le (hsymIdx sym)⟩
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]
          exact ⟨hcells, fun sym => Nat.le_succ_of_le (hsymIdx sym)⟩
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]
        exact ⟨hcells, fun sym => Nat.le_succ_of_le (hsymIdx sym)⟩
    · intro _ _ _ _ _ heq; simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> (try split at heq) <;>
      (try split at heq) <;> exact nomatch heq
  exact h4.1 i

/-- Helper: `Nat.toUInt16.toNat` preserves strict upper bounds.
    Since `n.toUInt16.toNat = n % UInt16.size ≤ n`, any upper bound on `n`
    transfers to `n.toUInt16.toNat`. -/
private theorem toUInt16_toNat_lt_of_lt {n m : Nat} (h : n < m) :
    n.toUInt16.toNat < m := by
  simp only [Nat.toUInt16_eq, UInt16.toNat_ofNat']
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) h

open Zstd.Native in
/-- When `buildFseTable` succeeds and the input distribution is non-empty,
    every cell's symbol index is less than `probs.size`.
    This is condition (b) of `ValidFseTable`.

    The proof threads the invariant through all four bind chains:
    - Initial cells have `symbol = 0 < probs.size` (by `hpos`)
    - Loops 1-2 set `symbol := sym.toUInt16` where `sym < probs.size`
    - Loop 3 doesn't modify cells
    - Loop 4 preserves symbol (`{ cells[i]!.symbol with ... }`) -/
theorem buildFseTable_symbol_lt (probs : Array Int32) (al : Nat)
    (table : FseTable) (h : buildFseTable probs al = .ok table)
    (hpos : 0 < probs.size)
    (i : Fin table.cells.size) :
    table.cells[i].symbol.toNat < probs.size := by
  simp only [buildFseTable] at h
  obtain ⟨v1, hloop1, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v2, hloop2, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v3, hloop3, h⟩ := Except.bind_eq_ok' h
  obtain ⟨v4, hloop4, h⟩ := Except.bind_eq_ok' h
  simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  show v4.fst[i].symbol.toNat < probs.size
  let P : FseCell → Prop := fun c => c.symbol.toNat < probs.size
  -- Initial cells: Array.replicate with default has symbol = 0
  have hinit : ∀ j : Fin (Array.replicate (1 <<< al) (default : FseCell)).size,
      P (Array.replicate (1 <<< al) (default : FseCell))[j] := by
    intro ⟨j, hj⟩; show P _
    simp only [Fin.getElem_fin, Array.getElem_replicate]; exact hpos
  -- Loop 1: preserves property (sets cells with { symbol := sym.toUInt16 })
  have h1 : ∀ j : Fin v1.fst.size, P v1.fst[j] := by
    apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, P s.fst[j])
      _ _ _ _ hinit _ _ hloop1
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · -- if h_sym : sym < probs.size
        split at heq
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
          rename_i h_sym hcond
          apply set!_preserves_forall hb; show P _
          exact toUInt16_toNat_lt_of_lt h_sym
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> exact nomatch heq
  -- Loop 2: preserves property (sets cells with { symbol := sym.toUInt16 })
  have h2 : ∀ j : Fin v2.fst.size, P v2.fst[j] := by
    apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, P s.fst[j])
      _ _ _ _ h1 _ _ hloop2
    · intro a b b' hb heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      · -- if h_sym : sym < probs.size
        rename_i ha_bound
        split at heq
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
        · split at heq
          · exact nomatch heq
          · rename_i _ _ hinner
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
            apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, P s.fst[j])
              _ _ _ _ hb _ _ hinner
            · intro a2 b2 b2' hb2 heq2
              rw [← ForInStep.yield.inj (Except.ok.inj heq2)]; dsimp only
              exact set!_preserves_forall hb2 (toUInt16_toNat_lt_of_lt ha_bound)
            · intro a2 b2 b2' hb2 heq2; exact nomatch heq2
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · intro _ _ _ _ heq; simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq <;> (try split at heq) <;> (try split at heq) <;> exact nomatch heq
  -- Loop 3 modifies only symbolCounts (v3 : Array Nat), not cells.
  -- Loop 4 starts with v2.fst as its initial cells.
  -- Loop 4: preserves symbol field ({ symbol := cells[i]!.symbol, ... })
  apply forIn_range_preserves (fun s => ∀ j : Fin s.fst.size, P s.fst[j])
    _ _ _ _ h2 _ _ hloop4
  · intro a b b' hb heq
    simp only [bind, Except.bind, pure, Except.pure] at heq
    split at heq
    · -- if h_i : i < cells.size
      split at heq
      · -- if h_sc
        split at heq
        · -- if h_si
          split at heq
          · -- count != 0: set! preserves symbol field
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]; dsimp only
            rename_i h_i _ _ _
            exact set!_preserves_forall hb (show P _ by
              show (b.fst[a]).symbol.toNat < probs.size
              exact hb ⟨a, h_i⟩)
          · -- count == 0
            rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
        · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
      · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
    · rw [← ForInStep.yield.inj (Except.ok.inj heq)]; exact hb
  · intro _ _ _ _ heq; simp only [bind, Except.bind, pure, Except.pure] at heq
    split at heq <;> (try split at heq) <;> (try split at heq) <;>
    (try split at heq) <;> exact nomatch heq

open Zstd.Native in
/-- When `buildFseTable` succeeds and the input distribution is non-empty,
    the resulting table satisfies `ValidFseTable`: size equals `1 <<< al`,
    all symbols are within bounds, and all `numBits` values are at most `al`.

    This composes `buildFseTable_cells_size`, `buildFseTable_symbol_lt`,
    and `buildFseTable_numBits_le`. -/
theorem buildFseTable_valid (probs : Array Int32) (al : Nat)
    (table : FseTable) (h : buildFseTable probs al = .ok table)
    (hpos : 0 < probs.size) :
    ValidFseTable table.cells al probs.size :=
  ⟨buildFseTable_cells_size probs al table h,
   fun i => buildFseTable_symbol_lt probs al table h hpos i,
   fun i => buildFseTable_numBits_le probs al table h i⟩

end Zstd.Spec.Fse
