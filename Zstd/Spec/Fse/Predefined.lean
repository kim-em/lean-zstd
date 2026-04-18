import Zstd.Spec.Fse.BuildTable

/-!
# Predefined FSE table structural properties

Theorems about `Zstd.Native.buildPredefinedFseTables`: success,
accuracy logs, and `ValidFseTable` composition for each of the three
predefined tables. -/

namespace Zstd.Spec.Fse

open Zstd.Native (FseTable)

/-! ## Structural properties of `buildPredefinedFseTables` -/

open Zstd.Native in
/-- `buildPredefinedFseTables` succeeds: the three predefined distributions
    are well-formed and `buildFseTable` accepts them.

    This follows from `buildFseTable_ok`, which shows `buildFseTable` always
    succeeds — its body contains only pure array operations and never throws. -/
theorem buildPredefinedFseTables_success :
    ∃ tables, buildPredefinedFseTables = Except.ok tables := by
  simp only [buildPredefinedFseTables]
  obtain ⟨ll, hll⟩ := buildFseTable_ok predefinedLitLenDistribution 6
  obtain ⟨ml, hml⟩ := buildFseTable_ok predefinedMatchLenDistribution 6
  obtain ⟨of, hof⟩ := buildFseTable_ok predefinedOffsetDistribution 5
  rw [hll, hml, hof]
  exact ⟨_, rfl⟩

open Zstd.Native in
/-- When `buildPredefinedFseTables` succeeds, the three tables have the
    expected accuracy logs: 6 for literal lengths, 6 for match lengths,
    and 5 for offsets. -/
theorem buildPredefinedFseTables_accuracyLogs :
    ∀ ll ml of, buildPredefinedFseTables = Except.ok (ll, ml, of) →
      ll.accuracyLog = 6 ∧ ml.accuracyLog = 6 ∧ of.accuracyLog = 5 := by
  intro ll ml of h
  simp only [buildPredefinedFseTables] at h
  obtain ⟨ll', hll, h⟩ := Except.bind_eq_ok' h
  obtain ⟨ml', hml, h⟩ := Except.bind_eq_ok' h
  obtain ⟨of', hof, h⟩ := Except.bind_eq_ok' h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨buildFseTable_accuracyLog_eq _ _ _ hll,
         buildFseTable_accuracyLog_eq _ _ _ hml,
         buildFseTable_accuracyLog_eq _ _ _ hof⟩

/-! ## Predefined FSE table `ValidFseTable` composition

Composes `buildFseTable_valid` with the concrete predefined distributions
to show each predefined table satisfies `ValidFseTable`. -/

open Zstd.Native in
/-- The predefined literal-length FSE table satisfies `ValidFseTable` with
    accuracy log 6 and 36 symbols. -/
theorem buildPredefinedFseTables_litLen_valid (ll ml of : FseTable)
    (h : buildPredefinedFseTables = .ok (ll, ml, of)) :
    ValidFseTable ll.cells 6 36 := by
  simp only [buildPredefinedFseTables] at h
  obtain ⟨ll', hll, h⟩ := Except.bind_eq_ok' h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok' h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok' h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, _, _⟩ := h
  exact buildFseTable_valid _ _ _ hll (by decide)

open Zstd.Native in
/-- The predefined match-length FSE table satisfies `ValidFseTable` with
    accuracy log 6 and 53 symbols. -/
theorem buildPredefinedFseTables_matchLen_valid (ll ml of : FseTable)
    (h : buildPredefinedFseTables = .ok (ll, ml, of)) :
    ValidFseTable ml.cells 6 53 := by
  simp only [buildPredefinedFseTables] at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok' h
  obtain ⟨ml', hml, h⟩ := Except.bind_eq_ok' h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok' h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl, _⟩ := h
  exact buildFseTable_valid _ _ _ hml (by decide)

open Zstd.Native in
/-- The predefined offset FSE table satisfies `ValidFseTable` with
    accuracy log 5 and 29 symbols. -/
theorem buildPredefinedFseTables_offset_valid (ll ml of : FseTable)
    (h : buildPredefinedFseTables = .ok (ll, ml, of)) :
    ValidFseTable of.cells 5 29 := by
  simp only [buildPredefinedFseTables] at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok' h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok' h
  obtain ⟨of', hof, h⟩ := Except.bind_eq_ok' h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, _, rfl⟩ := h
  exact buildFseTable_valid _ _ _ hof (by decide)

end Zstd.Spec.Fse
