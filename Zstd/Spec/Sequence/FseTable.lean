import Zstd.Native.Sequence
import Zstd.Spec.Fse

/-!
# `buildRleFseTable` and `resolveSingleFseTable` structural properties

Per-mode characterizations of `resolveSingleFseTable` (predefined, RLE,
repeat, fseCompressed) covering position advance, size bounds, and
`ValidFseTable` validity. The unified lemmas at the end (`_valid_ex`,
`_pos_ge`) combine all four modes for use in downstream composition.
-/

namespace Zstd.Native

open ZipCommon (BitReader)

/-! ## buildRleFseTable structural properties -/

/-- The accuracy log of an RLE FSE table is always 0. -/
theorem buildRleFseTable_accuracyLog (symbol : UInt8) :
    (buildRleFseTable symbol).accuracyLog = 0 := by
  rfl

/-- The RLE FSE table has exactly 1 cell. -/
theorem buildRleFseTable_cells_size (symbol : UInt8) :
    (buildRleFseTable symbol).cells.size = 1 := by
  rfl

/-- The RLE FSE table has a single cell, so any index into it must be 0. -/
private theorem buildRleFseTable_fin_eq_zero (symbol : UInt8)
    (i : Fin (buildRleFseTable symbol).cells.size) :
    i = ⟨0, by show 0 < 1; omega⟩ :=
  Fin.ext (by have : (buildRleFseTable symbol).cells.size = 1 := rfl; omega)

/-- The single cell's symbol in an RLE FSE table is within bounds. -/
theorem buildRleFseTable_symbol_lt (symbol : UInt8) (numSymbols : Nat)
    (hsym : symbol.toNat < numSymbols)
    (i : Fin (buildRleFseTable symbol).cells.size) :
    (buildRleFseTable symbol).cells[i].symbol.toNat < numSymbols := by
  have hi := buildRleFseTable_fin_eq_zero symbol i; subst hi
  show symbol.toUInt16.toNat < numSymbols
  rw [UInt8.toNat_toUInt16]
  exact hsym

/-- The RLE-constructed table satisfies the `ValidFseTable` predicate. -/
theorem buildRleFseTable_valid (symbol : UInt8) (numSymbols : Nat)
    (hsym : symbol.toNat < numSymbols) :
    Zstd.Spec.Fse.ValidFseTable (buildRleFseTable symbol).cells 0 numSymbols := by
  refine ⟨buildRleFseTable_cells_size symbol, buildRleFseTable_symbol_lt symbol numSymbols hsym, ?_⟩
  intro i; have hi := buildRleFseTable_fin_eq_zero symbol i; subst hi
  show (0 : UInt8).toNat ≤ 0; decide

/-! ## resolveSingleFseTable position properties -/

/-- In predefined mode, the position is unchanged. -/
theorem resolveSingleFseTable_predefined_pos (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .predefined maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos')) :
    pos' = pos := by
  simp only [resolveSingleFseTable, bind, Except.bind, pure, Except.pure] at h
  cases hbt : buildFseTable predefinedDist predefinedAccLog with
  | error e => rw [hbt] at h; exact nomatch h
  | ok tbl =>
    rw [hbt] at h
    exact (Prod.mk.inj (Except.ok.inj h)).2.symm

/-- In predefined mode, the returned position is at most `data.size`.
    Since predefined mode doesn't advance the position (`pos' = pos`),
    this follows directly from the input bound. -/
theorem resolveSingleFseTable_predefined_le_size (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .predefined maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos'))
    (hpos : pos ≤ data.size) :
    pos' ≤ data.size := by
  have := resolveSingleFseTable_predefined_pos _ _ _ _ _ _ _ _ _ h
  omega

/-- In RLE mode, the position advances by exactly 1. The RLE branch reads one byte
    at `pos` for the symbol and returns `(buildRleFseTable symbol, pos + 1)`. -/
theorem resolveSingleFseTable_rle_pos (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .rle maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos')) :
    pos' = pos + 1 := by
  simp only [resolveSingleFseTable, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm

/-- In RLE mode, the returned position is at most `data.size`.
    Success implies `data.size ≥ pos + 1` (from the guard), and
    `pos' = pos + 1`, so `pos' ≤ data.size`. -/
theorem resolveSingleFseTable_rle_le_size (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .rle maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos')) :
    pos' ≤ data.size := by
  have hpos_eq := resolveSingleFseTable_rle_pos _ _ _ _ _ _ _ _ _ h
  -- Extract the guard: success means ¬(data.size < pos + 1)
  simp only [resolveSingleFseTable, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · rename_i hguard
    omega

/-- In repeat mode, the position is unchanged. The repeat branch returns
    `(prevTable.get!, pos)` without consuming any data. -/
theorem resolveSingleFseTable_repeat_pos (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .repeat maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos')) :
    pos' = pos := by
  simp only [resolveSingleFseTable, pure, Except.pure] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.symm
  · exact nomatch h

/-- In repeat mode, the returned position is at most `data.size`.
    Since repeat mode doesn't advance the position (`pos' = pos`),
    this follows directly from the input bound. -/
theorem resolveSingleFseTable_repeat_le_size (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .repeat maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos'))
    (hpos : pos ≤ data.size) :
    pos' ≤ data.size := by
  have := resolveSingleFseTable_repeat_pos _ _ _ _ _ _ _ _ _ h
  omega

/-- Decompose a successful `resolveSingleFseTable` call in fseCompressed mode into its
    constituent `decodeFseDistribution` and `buildFseTable` successes, plus the
    position computation. -/
private theorem resolveSingleFseTable_fseCompressed_destruct (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .fseCompressed maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos')) :
    ∃ (probs : Array Int32) (accLog : Nat) (br' : BitReader),
      decodeFseDistribution ⟨data, pos, 0⟩ maxSymbols maxAccLog = .ok (probs, accLog, br') ∧
      buildFseTable probs accLog = .ok table ∧
      pos' = (if br'.bitOff == 0 then br'.pos else br'.pos + 1) := by
  simp only [resolveSingleFseTable, pure, Except.pure] at h
  cases hfse : decodeFseDistribution { data, pos, bitOff := 0 } maxSymbols maxAccLog with
  | error e => rw [hfse] at h; dsimp only [Bind.bind, Except.bind] at h; exact nomatch h
  | ok val =>
    obtain ⟨probs, accLog, br'⟩ := val
    rw [hfse] at h; dsimp only [Bind.bind, Except.bind] at h
    cases hbt : buildFseTable probs accLog with
    | error e => rw [hbt] at h; dsimp only [Bind.bind, Except.bind] at h; exact nomatch h
    | ok tbl =>
      rw [hbt] at h; dsimp only [Bind.bind, Except.bind] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨probs, accLog, br', rfl, hbt, rfl⟩

/-- In fseCompressed mode, the returned position is strictly greater than the input.
    The branch creates a BitReader at `(pos, bitOff=0)`, calls `decodeFseDistribution`
    (which reads ≥4 bits for the accuracy log), then rounds up to the next byte
    boundary. Since ≥4 bits are consumed starting from bit offset 0, the resulting
    byte position must exceed the input. -/
theorem resolveSingleFseTable_fseCompressed_pos_gt (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .fseCompressed maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos')) :
    pos' > pos := by
  obtain ⟨_, _, br', hfse, _, rfl⟩ :=
    resolveSingleFseTable_fseCompressed_destruct _ _ _ _ _ _ _ _ _ h
  have ⟨hge, _⟩ := Zstd.Spec.Fse.decodeFseDistribution_bitPos_ge hfse
    (by omega : (0 : Nat) < 8)
  simp only [BitReader.bitPos] at hge
  by_cases hbo : br'.bitOff == 0
  · simp only [hbo, ↓reduceIte]; have := eq_of_beq hbo; rw [this] at hge; omega
  · simp only [hbo, Bool.false_eq_true, ↓reduceIte]; omega

/-! ## resolveSingleFseTable validity — per-mode ValidFseTable proofs -/

/-- In predefined mode, the returned table satisfies `ValidFseTable` with the predefined
    distribution's accuracy log and symbol count, provided the distribution is non-empty. -/
theorem resolveSingleFseTable_predefined_valid (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .predefined maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos'))
    (hpos : 0 < predefinedDist.size) :
    Zstd.Spec.Fse.ValidFseTable table.cells predefinedAccLog predefinedDist.size := by
  simp only [resolveSingleFseTable, pure, Except.pure] at h
  cases hbt : buildFseTable predefinedDist predefinedAccLog with
  | error e => rw [hbt] at h; exact nomatch h
  | ok tbl =>
    rw [hbt] at h
    have htable : tbl = table := (Prod.mk.inj (Except.ok.inj h)).1
    cases htable
    exact Zstd.Spec.Fse.buildFseTable_valid _ _ _ hbt hpos

/-- In RLE mode, the returned table satisfies `ValidFseTable` with accuracy log 0
    and 256 symbols. Since the symbol is a `UInt8`, `symbol.toNat < 256` always holds. -/
theorem resolveSingleFseTable_rle_valid (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .rle maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos')) :
    Zstd.Spec.Fse.ValidFseTable table.cells 0 256 := by
  simp only [resolveSingleFseTable, pure, Except.pure] at h
  split at h
  · exact nomatch h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact buildRleFseTable_valid _ 256 (UInt8.toNat_lt _)

/-- In repeat mode, the returned table IS the previous table. If the previous table
    satisfies `ValidFseTable`, so does the returned table. -/
theorem resolveSingleFseTable_repeat_valid (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .repeat maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos'))
    (al ns : Nat)
    (hprev : ∀ t, prevTable = some t → Zstd.Spec.Fse.ValidFseTable t.cells al ns) :
    Zstd.Spec.Fse.ValidFseTable table.cells al ns := by
  simp only [resolveSingleFseTable, pure, Except.pure] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact hprev _ rfl
  · exact nomatch h

/-- In fseCompressed mode, the returned table satisfies `ValidFseTable` for the decoded
    distribution. The existential quantification is needed because `probs` and `accLog`
    are read from the bitstream (not input parameters). -/
theorem resolveSingleFseTable_fseCompressed_valid (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat)
    (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable)
    (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable .fseCompressed maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos')) :
    ∃ (probs : Array Int32) (accLog : Nat),
      Zstd.Spec.Fse.ValidFseTable table.cells accLog probs.size := by
  obtain ⟨probs, accLog, _, hfse, hbt, _⟩ :=
    resolveSingleFseTable_fseCompressed_destruct _ _ _ _ _ _ _ _ _ h
  exact ⟨probs, accLog,
    Zstd.Spec.Fse.buildFseTable_valid _ _ _ hbt
      (Zstd.Spec.Fse.decodeFseDistribution_size_pos hfse)⟩

/-! ## resolveSingleFseTable unified validity -/

/-- Across all four compression modes, when `resolveSingleFseTable` succeeds, the returned
    table satisfies `ValidFseTable` for some accuracy log and symbol count. Requires
    non-empty predefined distribution (for predefined mode) and validity of previous table
    (for repeat mode). -/
theorem resolveSingleFseTable_valid_ex (mode : SequenceCompressionMode) (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat) (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable) (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable mode maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos'))
    (hpos : 0 < predefinedDist.size)
    (hprev : ∀ t, prevTable = some t → ∃ al ns, Zstd.Spec.Fse.ValidFseTable t.cells al ns) :
    ∃ al ns, Zstd.Spec.Fse.ValidFseTable table.cells al ns := by
  cases mode with
  | predefined =>
    exact ⟨predefinedAccLog, predefinedDist.size,
      resolveSingleFseTable_predefined_valid _ _ _ _ _ _ _ _ _ h hpos⟩
  | rle =>
    exact ⟨0, 256, resolveSingleFseTable_rle_valid _ _ _ _ _ _ _ _ _ h⟩
  | «repeat» =>
    -- In repeat mode, table = prevTable.get!
    simp only [resolveSingleFseTable, pure, Except.pure] at h
    cases hpt : prevTable with
    | none => rw [hpt] at h; exact nomatch h
    | some t =>
      rw [hpt] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact hprev t hpt
  | fseCompressed =>
    obtain ⟨probs, accLog, hv⟩ := resolveSingleFseTable_fseCompressed_valid _ _ _ _ _ _ _ _ _ h
    exact ⟨accLog, probs.size, hv⟩

/-! ## resolveSingleFseTable unified position monotonicity -/

/-- Across all four compression modes, the returned position is at least the input position.
    This unifies predefined (=), rle (+1), repeat (=), and fseCompressed (>). -/
theorem resolveSingleFseTable_pos_ge (mode : SequenceCompressionMode) (maxSymbols maxAccLog : Nat)
    (data : ByteArray) (pos : Nat) (predefinedDist : Array Int32) (predefinedAccLog : Nat)
    (prevTable : Option FseTable) (table : FseTable) (pos' : Nat)
    (h : resolveSingleFseTable mode maxSymbols maxAccLog data pos
           predefinedDist predefinedAccLog prevTable = .ok (table, pos')) :
    pos' ≥ pos := by
  cases mode with
  | predefined =>
    have := resolveSingleFseTable_predefined_pos _ _ _ _ _ _ _ _ _ h
    omega
  | rle =>
    have := resolveSingleFseTable_rle_pos _ _ _ _ _ _ _ _ _ h
    omega
  | «repeat» =>
    have := resolveSingleFseTable_repeat_pos _ _ _ _ _ _ _ _ _ h
    omega
  | fseCompressed =>
    have := resolveSingleFseTable_fseCompressed_pos_gt _ _ _ _ _ _ _ _ _ h
    omega

end Zstd.Native
