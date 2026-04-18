import Zstd.Spec.Sequence.FseTable

/-!
# `resolveSequenceFseTables` composition lemmas

Threading three `resolveSingleFseTable` calls — litLen, offset, matchLen —
through the composite `resolveSequenceFseTables`. The decomposition lemma
splits a successful composite call into its three pieces; the position
and validity lemmas compose the per-table results; the completeness
lemma goes the other way, building a composite success from three
per-table successes.
-/

namespace Zstd.Native

/-! ## resolveSequenceFseTables decomposition -/

/-- Decompose a successful `resolveSequenceFseTables` call into its three
    constituent `resolveSingleFseTable` successes with threaded positions. -/
private theorem resolveSequenceFseTables_destruct (modes : SequenceCompressionModes)
    (data : ByteArray) (pos : Nat) (prev : PrevFseTables)
    (llTable ofTable mlTable : FseTable) (pos' : Nat)
    (h : resolveSequenceFseTables modes data pos prev = .ok (llTable, ofTable, mlTable, pos')) :
    ∃ (v₁ v₂ v₃ : FseTable × Nat),
      resolveSingleFseTable modes.litLenMode 36 9 data pos
        predefinedLitLenDistribution 6 prev.litLen = .ok v₁ ∧
      resolveSingleFseTable modes.offsetMode 32 8 data v₁.2
        predefinedOffsetDistribution 5 prev.offset = .ok v₂ ∧
      resolveSingleFseTable modes.matchLenMode 53 9 data v₂.2
        predefinedMatchLenDistribution 6 prev.matchLen = .ok v₃ ∧
      v₁.1 = llTable ∧ v₂.1 = ofTable ∧ v₃.1 = mlTable ∧ v₃.2 = pos' := by
  simp only [resolveSequenceFseTables, bind, Except.bind, pure, Except.pure] at h
  cases hll : resolveSingleFseTable modes.litLenMode 36 9 data pos
      predefinedLitLenDistribution 6 prev.litLen with
  | error e => rw [hll] at h; exact nomatch h
  | ok val₁ =>
    rw [hll] at h; dsimp only [Bind.bind, Except.bind] at h
    cases hof : resolveSingleFseTable modes.offsetMode 32 8 data val₁.2
        predefinedOffsetDistribution 5 prev.offset with
    | error e => rw [hof] at h; exact nomatch h
    | ok val₂ =>
      rw [hof] at h; dsimp only [Bind.bind, Except.bind] at h
      cases hml : resolveSingleFseTable modes.matchLenMode 53 9 data val₂.2
          predefinedMatchLenDistribution 6 prev.matchLen with
      | error e => rw [hml] at h; exact nomatch h
      | ok val₃ =>
        rw [hml] at h; dsimp only [Bind.bind, Except.bind] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨val₁, val₂, val₃, rfl, hof, hml, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-! ## resolveSequenceFseTables position composition -/

/-- The 3-table resolver doesn't decrease position. Composes three
    `resolveSingleFseTable_pos_ge` applications via transitivity. -/
theorem resolveSequenceFseTables_pos_ge (modes : SequenceCompressionModes)
    (data : ByteArray) (pos : Nat) (prev : PrevFseTables)
    (llTable ofTable mlTable : FseTable) (pos' : Nat)
    (h : resolveSequenceFseTables modes data pos prev = .ok (llTable, ofTable, mlTable, pos')) :
    pos' ≥ pos := by
  obtain ⟨v₁, v₂, v₃, hll, hof, hml, -, -, -, rfl⟩ :=
    resolveSequenceFseTables_destruct _ _ _ _ _ _ _ _ h
  have h₁ := resolveSingleFseTable_pos_ge _ _ _ _ _ _ _ _ _ _ hll
  have h₂ := resolveSingleFseTable_pos_ge _ _ _ _ _ _ _ _ _ _ hof
  have h₃ := resolveSingleFseTable_pos_ge _ _ _ _ _ _ _ _ _ _ hml
  omega

/-! ## resolveSequenceFseTables validity composition -/

/-- When `resolveSequenceFseTables` succeeds, all three returned FSE tables satisfy
    `ValidFseTable` for some accuracy log and symbol count. Requires that any previous
    tables (for repeat mode) are also valid. Composes three applications of
    `resolveSingleFseTable_valid_ex` — one for each of litLen, offset, matchLen. -/
theorem resolveSequenceFseTables_valid (modes : SequenceCompressionModes)
    (data : ByteArray) (pos : Nat) (prev : PrevFseTables)
    (llTable ofTable mlTable : FseTable) (pos' : Nat)
    (h : resolveSequenceFseTables modes data pos prev = .ok (llTable, ofTable, mlTable, pos'))
    (hprevLL : ∀ t, prev.litLen = some t → ∃ al ns, Zstd.Spec.Fse.ValidFseTable t.cells al ns)
    (hprevOF : ∀ t, prev.offset = some t → ∃ al ns, Zstd.Spec.Fse.ValidFseTable t.cells al ns)
    (hprevML : ∀ t, prev.matchLen = some t → ∃ al ns, Zstd.Spec.Fse.ValidFseTable t.cells al ns) :
    (∃ al ns, Zstd.Spec.Fse.ValidFseTable llTable.cells al ns) ∧
    (∃ al ns, Zstd.Spec.Fse.ValidFseTable ofTable.cells al ns) ∧
    (∃ al ns, Zstd.Spec.Fse.ValidFseTable mlTable.cells al ns) := by
  obtain ⟨_, _, _, hll, hof, hml, rfl, rfl, rfl, -⟩ :=
    resolveSequenceFseTables_destruct _ _ _ _ _ _ _ _ h
  exact ⟨resolveSingleFseTable_valid_ex _ _ _ _ _ _ _ _ _ _ hll (by decide) hprevLL,
         resolveSingleFseTable_valid_ex _ _ _ _ _ _ _ _ _ _ hof (by decide) hprevOF,
         resolveSingleFseTable_valid_ex _ _ _ _ _ _ _ _ _ _ hml (by decide) hprevML⟩

/-! ## resolveSequenceFseTables completeness -/

/-- When each of the three `resolveSingleFseTable` calls succeeds, the composed
    `resolveSequenceFseTables` succeeds and returns the exact output. The three
    hypotheses capture position-threading: `pos → pos1 → pos2 → pos3`. -/
theorem resolveSequenceFseTables_succeeds
    (modes : SequenceCompressionModes) (data : ByteArray) (pos : Nat)
    (prev : PrevFseTables)
    (litLenTable : FseTable) (pos1 : Nat)
    (offsetTable : FseTable) (pos2 : Nat)
    (matchLenTable : FseTable) (pos3 : Nat)
    (hlit : resolveSingleFseTable modes.litLenMode 36 9 data pos
            predefinedLitLenDistribution 6 prev.litLen = .ok (litLenTable, pos1))
    (hoff : resolveSingleFseTable modes.offsetMode 32 8 data pos1
            predefinedOffsetDistribution 5 prev.offset = .ok (offsetTable, pos2))
    (hml : resolveSingleFseTable modes.matchLenMode 53 9 data pos2
           predefinedMatchLenDistribution 6 prev.matchLen = .ok (matchLenTable, pos3)) :
    resolveSequenceFseTables modes data pos prev =
      .ok (litLenTable, offsetTable, matchLenTable, pos3) := by
  simp only [resolveSequenceFseTables, bind, Except.bind, pure, Except.pure, hlit, hoff, hml]

end Zstd.Native
