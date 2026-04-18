import Zstd.Native.Sequence

/-!
# Sequence validity predicates and `resolveOffset` properties

Declarative validity predicates for decoded sequences — `ValidSequence`,
`ValidSequenceList`, `ValidOffsetHistory` — plus the characterizations
of `resolveOffset` that connect them to the implementation:

* per-case value formulas (repeat 1/2/3, shifted 1/2/3, large offsets),
* positivity and history-validity preservation,
* the unified positivity theorem `resolveOffset_positive_all`,
* loop-level preservation of `ValidOffsetHistory` under
  `executeSequences.loop`.
-/

namespace Zstd.Spec.Sequence

open Zstd.Native (ZstdSequence resolveOffset)

/-! ## Validity predicates -/

/-- A single decoded sequence is valid in the context of the current output size
    and remaining literals:
    (a) the literal copy doesn't exceed available literals,
    (b) the resolved offset is positive (no zero offsets), and
    (c) the resolved offset doesn't reach beyond the output produced so far
        plus the literals this sequence will append. -/
def ValidSequence (seq : ZstdSequence) (outputSoFar : Nat) (literalsRemaining : Nat) : Prop :=
  seq.literalLength ≤ literalsRemaining ∧
  seq.offset > 0 ∧
  seq.offset ≤ outputSoFar + seq.literalLength

instance : Decidable (ValidSequence seq outputSoFar literalsRemaining) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A sequence array is valid with respect to a total literals count when the
    sum of all `literalLength` fields does not exceed the total available
    literals. This is a necessary condition for `executeSequences` to succeed
    without a "not enough literals" error. -/
def ValidSequenceList (seqs : Array ZstdSequence) (totalLiterals : Nat) : Prop :=
  seqs.foldl (fun acc s => acc + s.literalLength) 0 ≤ totalLiterals

instance : Decidable (ValidSequenceList seqs totalLiterals) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A valid offset history has exactly 3 entries, all positive (RFC 8878 §3.1.1.5).
    The initial offset history is `#[1, 4, 8]`. Uses `get!` to match the
    implementation's `history[i]!` access pattern. -/
def ValidOffsetHistory (history : Array Nat) : Prop :=
  history.size = 3 ∧ history[0]! > 0 ∧ history[1]! > 0 ∧ history[2]! > 0

instance {history : Array Nat} : Decidable (ValidOffsetHistory history) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-! ## Correctness theorems -/

/-- `resolveOffset` preserves the offset history size: if the input history has
    exactly 3 entries, the output history also has exactly 3 entries. This follows
    from every branch of the implementation constructing `#[_, _, _]` or returning
    the history unchanged. -/
theorem resolveOffset_history_size (rawOffset : Nat) (history : Array Nat) (litLen : Nat)
    (h : history.size = 3) :
    (resolveOffset rawOffset history litLen).2.size = 3 := by
  unfold resolveOffset
  simp only [show ¬(history.size < 3) from by omega, dite_false]
  -- Every branch returns either a literal #[_, _, _] (size = 3 by rfl)
  -- or the unchanged history (size = 3 by h).
  split <;> (try rfl)
  split <;> (split <;> first | rfl | exact h)

/-- When `resolveOffset` is called with `rawOffset > 3`, the resolved offset
    is `rawOffset - 3`, which is positive. -/
theorem resolveOffset_positive_large (rawOffset : Nat) (history : Array Nat) (litLen : Nat)
    (hraw : rawOffset > 3) :
    (resolveOffset rawOffset history litLen).1 > 0 := by
  unfold resolveOffset
  split -- history.size < 3
  · omega
  · dsimp only; omega

/-- When `resolveOffset` is called with a valid offset history, `rawOffset > 0`,
    and `literalLength > 0`, the resolved offset is positive. This covers the
    normal repeat offset case (rawOffset 1–3 returns a history entry, all positive
    by `ValidOffsetHistory`) and actual offsets (rawOffset > 3 gives rawOffset - 3 > 0).
    The `literalLength = 0` case is excluded because rawOffset = 3 with litLen = 0
    gives `history[0] - 1` which can be 0 when `history[0] = 1`. -/
theorem resolveOffset_positive_litLen_pos (rawOffset : Nat) (history : Array Nat) (litLen : Nat)
    (hraw : rawOffset > 0) (hvalid : ValidOffsetHistory history) (hlit : litLen > 0) :
    (resolveOffset rawOffset history litLen).1 > 0 := by
  obtain ⟨hsz, h0pos, h1pos, h2pos⟩ := hvalid
  -- Case split on rawOffset: 0 (impossible), 1, 2, 3, or ≥ 4
  rcases rawOffset with _ | _ | _ | _ | n
  · omega  -- rawOffset = 0, contradicts hraw
  · -- rawOffset = 1, litLen > 0: returns history[0]!
    simp only [resolveOffset, show ¬(history.size < 3) from by omega, dite_false,
      show ¬(1 > 3) from by omega, show litLen > 0 from hlit, ↓reduceIte, ← getElem!_pos]
    exact h0pos
  · -- rawOffset = 2, litLen > 0: returns history[1]!
    simp only [resolveOffset, show ¬(history.size < 3) from by omega, dite_false,
      show ¬(2 > 3) from by omega, show litLen > 0 from hlit, ↓reduceIte, ← getElem!_pos]
    exact h1pos
  · -- rawOffset = 3, litLen > 0: returns history[2]!
    simp only [resolveOffset, show ¬(history.size < 3) from by omega, dite_false,
      show ¬(3 > 3) from by omega, show litLen > 0 from hlit, ↓reduceIte, ← getElem!_pos]
    exact h2pos
  · -- rawOffset = n + 4 > 3: offset = n + 1 > 0
    simp only [resolveOffset, show ¬(history.size < 3) from by omega, dite_false,
      show n + 4 > 3 from by omega, ↓reduceIte]
    omega

/-- When `rawOffset = 1`, `history.size = 3`, and `literalLength > 0`, the resolved
    offset equals `history[0]!` (the most recent offset). This is the exact value
    returned by the RFC 8878 §3.1.1.5 repeat offset mechanism for code 1. -/
theorem resolveOffset_repeat1_val (history : Array Nat) (litLen : Nat)
    (_hsize : history.size = 3) (hlit : litLen > 0) :
    (resolveOffset 1 history litLen).1 = history[0]! := by
  simp only [resolveOffset, show ¬(history.size < 3) from by omega, dite_false,
    show ¬(1 > 3) from by omega, show litLen > 0 from hlit, ↓reduceIte, ← getElem!_pos]

/-- When `rawOffset = 2`, `history.size = 3`, and `literalLength > 0`, the resolved
    offset equals `history[1]!` (the second most recent offset). -/
theorem resolveOffset_repeat2_val (history : Array Nat) (litLen : Nat)
    (_hsize : history.size = 3) (hlit : litLen > 0) :
    (resolveOffset 2 history litLen).1 = history[1]! := by
  simp only [resolveOffset, show ¬(history.size < 3) from by omega, dite_false,
    show ¬(2 > 3) from by omega, show litLen > 0 from hlit, ↓reduceIte, ← getElem!_pos]

/-- When `rawOffset = 3`, `history.size = 3`, and `literalLength > 0`, the resolved
    offset equals `history[2]!` (the third most recent offset). -/
theorem resolveOffset_repeat3_val (history : Array Nat) (litLen : Nat)
    (_hsize : history.size = 3) (hlit : litLen > 0) :
    (resolveOffset 3 history litLen).1 = history[2]! := by
  simp only [resolveOffset, show ¬(history.size < 3) from by omega, dite_false,
    show ¬(3 > 3) from by omega, show litLen > 0 from hlit, ↓reduceIte, ← getElem!_pos]

/-- When `rawOffset = 1`, `history.size = 3`, and `literalLength = 0` (shifted mode),
    the resolved offset equals `history[1]!` (second most recent) and the history
    becomes `#[history[1]!, history[0]!, history[2]!]`. RFC 8878 §3.1.1.5 shifted case. -/
theorem resolveOffset_shifted1_val (history : Array Nat)
    (_hsize : history.size = 3) :
    (resolveOffset 1 history 0).1 = history[1]!
    ∧ (resolveOffset 1 history 0).2 = #[history[1]!, history[0]!, history[2]!] := by
  simp only [resolveOffset, show ¬(history.size < 3) from by omega, dite_false,
    show ¬(1 > 3) from by omega, show ¬(0 > 0) from by omega,
    ↓reduceIte, ← getElem!_pos, and_self]

/-- When `rawOffset = 2`, `history.size = 3`, and `literalLength = 0` (shifted mode),
    the resolved offset equals `history[2]!` (third most recent) and the history
    becomes `#[history[2]!, history[0]!, history[1]!]`. RFC 8878 §3.1.1.5 shifted case. -/
theorem resolveOffset_shifted2_val (history : Array Nat)
    (_hsize : history.size = 3) :
    (resolveOffset 2 history 0).1 = history[2]!
    ∧ (resolveOffset 2 history 0).2 = #[history[2]!, history[0]!, history[1]!] := by
  simp only [resolveOffset, show ¬(history.size < 3) from by omega, dite_false,
    show ¬(2 > 3) from by omega, show ¬(0 > 0) from by omega,
    ↓reduceIte, ← getElem!_pos, and_self]

/-- When `rawOffset = 3`, `history.size = 3`, and `literalLength = 0` (shifted mode),
    the resolved offset equals `history[0]! - 1` (most recent minus one) and the history
    becomes `#[history[0]! - 1, history[1]!, history[2]!]`. RFC 8878 §3.1.1.5 shifted case.
    This is the special case used for run-length encoding patterns. -/
theorem resolveOffset_shifted3_val (history : Array Nat)
    (_hsize : history.size = 3) :
    (resolveOffset 3 history 0).1 = history[0]! - 1
    ∧ (resolveOffset 3 history 0).2 = #[history[0]! - 1, history[1]!, history[2]!] := by
  simp only [resolveOffset, show ¬(history.size < 3) from by omega, dite_false,
    show ¬(3 > 3) from by omega, show ¬(0 > 0) from by omega,
    ↓reduceIte, ← getElem!_pos, and_self]

/-- Any 3-element array of positive naturals is a `ValidOffsetHistory`. -/
private theorem validOffsetHistory_mk3 (a b c : Nat) (ha : a > 0) (hb : b > 0) (hc : c > 0) :
    ValidOffsetHistory #[a, b, c] := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> simp only [List.size_toArray, List.length_cons, List.length_nil,
    Nat.zero_add, Nat.reduceAdd, Nat.reduceLT, getElem!_pos,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    gt_iff_lt] <;> omega

/-- When `rawOffset > 3` and input has `ValidOffsetHistory`, the output history
    also satisfies `ValidOffsetHistory`. The new history is
    `#[rawOffset - 3, history[0]!, history[1]!]`, all positive. -/
theorem resolveOffset_history_valid_large (rawOffset litLen : Nat)
    (history : Array Nat) (hh : ValidOffsetHistory history)
    (hr : rawOffset > 3) :
    ValidOffsetHistory (resolveOffset rawOffset history litLen).2 := by
  obtain ⟨hsz, h0pos, h1pos, _⟩ := hh
  simp only [resolveOffset, show ¬(history.size < 3) from by omega, dite_false,
    hr, ↓reduceIte, ← getElem!_pos]
  exact validOffsetHistory_mk3 _ _ _ (by omega) h0pos h1pos

/-- For repeat codes (rawOffset ∈ {1,2,3}), when input has `ValidOffsetHistory`
    and for the shifted rawOffset=3 case `history[0]! ≥ 2`, the output history
    satisfies `ValidOffsetHistory`. Covers both normal (litLen > 0) and shifted
    (litLen = 0) repeat offset modes per RFC 8878 §3.1.1.5. -/
theorem resolveOffset_history_valid_repeat (rawOffset litLen : Nat)
    (history : Array Nat) (hh : ValidOffsetHistory history)
    (hr : rawOffset > 0) (hr' : rawOffset ≤ 3)
    (hshift : litLen = 0 ∧ rawOffset = 3 → history[0]! ≥ 2) :
    ValidOffsetHistory (resolveOffset rawOffset history litLen).2 := by
  obtain ⟨hsz, h0pos, h1pos, h2pos⟩ := hh
  rcases rawOffset with _ | _ | _ | _ | n
  · omega  -- rawOffset = 0
  · -- rawOffset = 1
    unfold resolveOffset
    simp only [show ¬(history.size < 3) from by omega, dite_false,
      show ¬(1 > 3) from by omega, ↓reduceIte, ← getElem!_pos]
    split
    · exact ⟨hsz, h0pos, h1pos, h2pos⟩  -- litLen > 0: history unchanged
    · exact validOffsetHistory_mk3 _ _ _ h1pos h0pos h2pos
  · -- rawOffset = 2
    unfold resolveOffset
    simp only [show ¬(history.size < 3) from by omega, dite_false,
      show ¬(2 > 3) from by omega, ↓reduceIte, ← getElem!_pos]
    split
    · exact validOffsetHistory_mk3 _ _ _ h1pos h0pos h2pos
    · exact validOffsetHistory_mk3 _ _ _ h2pos h0pos h1pos
  · -- rawOffset = 3
    unfold resolveOffset
    simp only [show ¬(history.size < 3) from by omega, dite_false,
      show ¬(3 > 3) from by omega, ↓reduceIte, ← getElem!_pos]
    split
    · exact validOffsetHistory_mk3 _ _ _ h2pos h0pos h1pos
    · have h02 := hshift ⟨by omega, rfl⟩
      exact validOffsetHistory_mk3 _ _ _ (by omega) h1pos h2pos
  · omega  -- rawOffset ≥ 4

/-- When `resolveOffset` returns a nonzero offset and the input history is valid,
    the output history is also valid. Unifies `resolveOffset_history_valid_large`
    and `resolveOffset_history_valid_repeat` into a single lemma whose precondition
    matches the `executeSequences.loop` guard (`if offset == 0 then .error ...`). -/
theorem resolveOffset_history_valid_of_fst_ne_zero
    (rawOffset litLen : Nat) (history : Array Nat)
    (hh : ValidOffsetHistory history)
    (hne : (resolveOffset rawOffset history litLen).1 ≠ 0) :
    ValidOffsetHistory (resolveOffset rawOffset history litLen).2 := by
  by_cases hr : rawOffset > 3
  · exact resolveOffset_history_valid_large rawOffset litLen history hh hr
  · -- rawOffset ≤ 3
    by_cases hr0 : rawOffset = 0
    · -- rawOffset = 0: resolveOffset returns (1, history), history unchanged
      subst hr0
      have hsz := hh.1
      simp only [resolveOffset, show ¬(history.size < 3) from by omega, dite_false,
        show ¬(0 > 3) from by omega, ↓reduceIte]
      split <;> exact hh
    · -- rawOffset ∈ {1, 2, 3}
      apply resolveOffset_history_valid_repeat rawOffset litLen history hh (by omega) (by omega)
      intro ⟨hlit0, hraw3⟩
      -- litLen = 0 ∧ rawOffset = 3: resolveOffset returns history[0]! - 1
      subst hraw3; subst hlit0
      have := (resolveOffset_shifted3_val history hh.1).1
      -- hne : (resolveOffset 3 history 0).1 ≠ 0, and .1 = history[0]! - 1
      rw [this] at hne
      omega

/-- When `executeSequences.loop` succeeds and the input offset history is valid,
    the output offset history is also valid. Threads `ValidOffsetHistory` through the
    sequence loop by applying `resolveOffset_history_valid_of_fst_ne_zero` at each
    step (the loop's `if offset == 0 then .error` guard ensures the precondition). -/
theorem executeSequences_loop_history_valid
    (seqs : List ZstdSequence) (literals : ByteArray)
    (output : ByteArray) (history : Array Nat) (litPos windowSize : Nat)
    (output' : ByteArray) (history' : Array Nat) (litPos' : Nat)
    (hvalid : ValidOffsetHistory history)
    (h : Zstd.Native.executeSequences.loop seqs literals output history litPos windowSize
         = .ok (output', history', litPos')) :
    ValidOffsetHistory history' := by
  induction seqs generalizing output history litPos with
  | nil =>
    rw [Zstd.Native.executeSequences.loop.eq_1] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl, _⟩ := h
    exact hvalid
  | cons seq rest ih =>
    rw [Zstd.Native.executeSequences.loop.eq_2] at h
    split at h; · exact nomatch h
    dsimp only [letFun] at h
    split at h; · exact nomatch h
    split at h; · exact nomatch h
    split at h; · exact nomatch h
    exact ih _ _ _ (resolveOffset_history_valid_of_fst_ne_zero _ _ _ hvalid (by
        simp only [ne_eq, beq_iff_eq] at *; assumption)) h

/-- The loop preserves the history array size. Uses the weaker hypothesis
    `history.size = 3` rather than full `ValidOffsetHistory`. -/
theorem executeSequences_loop_history_size
    (seqs : List ZstdSequence) (literals : ByteArray)
    (output : ByteArray) (history : Array Nat) (litPos windowSize : Nat)
    (output' : ByteArray) (history' : Array Nat) (litPos' : Nat)
    (hsize : history.size = 3)
    (h : Zstd.Native.executeSequences.loop seqs literals output history litPos windowSize
         = .ok (output', history', litPos')) :
    history'.size = 3 := by
  induction seqs generalizing output history litPos with
  | nil =>
    rw [Zstd.Native.executeSequences.loop.eq_1] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl, _⟩ := h
    exact hsize
  | cons seq rest ih =>
    rw [Zstd.Native.executeSequences.loop.eq_2] at h
    split at h; · exact nomatch h
    dsimp only [letFun] at h
    split at h; · exact nomatch h
    split at h; · exact nomatch h
    split at h; · exact nomatch h
    exact ih _ _ _ (resolveOffset_history_size _ _ _ hsize) h

/-- For shifted repeat codes 1–2 (rawOffset ∈ {1,2}, literalLength = 0),
    `ValidOffsetHistory` implies the resolved offset is positive. Shifted code 1
    returns `history[1]!` and shifted code 2 returns `history[2]!`, both positive
    by `ValidOffsetHistory`. The shifted code 3 case (`history[0]! - 1`) is excluded
    because it can be 0 when `history[0]! = 1`. -/
theorem resolveOffset_positive_shifted12 (rawOffset : Nat) (history : Array Nat)
    (hraw : rawOffset > 0) (hraw' : rawOffset ≤ 2)
    (hvalid : ValidOffsetHistory history) :
    (resolveOffset rawOffset history 0).1 > 0 := by
  obtain ⟨hsz, _, h1pos, h2pos⟩ := hvalid
  rcases rawOffset with _ | _ | _ | n
  · omega  -- rawOffset = 0
  · -- rawOffset = 1: shifted → history[1]!
    simp only [resolveOffset, show ¬(history.size < 3) from by omega, dite_false,
      show ¬(1 > 3) from by omega, show ¬(0 > 0) from by omega,
      ↓reduceIte, ← getElem!_pos]
    exact h1pos
  · -- rawOffset = 2: shifted → history[2]!
    simp only [resolveOffset, show ¬(history.size < 3) from by omega, dite_false,
      show ¬(2 > 3) from by omega, show ¬(0 > 0) from by omega,
      ↓reduceIte, ← getElem!_pos]
    exact h2pos
  · omega  -- rawOffset ≥ 3

/-- Unified positivity theorem for `resolveOffset`: covers all cases where the
    resolved offset is guaranteed positive. This subsumes `resolveOffset_positive_large`
    (rawOffset > 3), `resolveOffset_positive_litLen_pos` (litLen > 0), and
    `resolveOffset_positive_shifted12` (shifted codes 1–2).

    The only case requiring an extra hypothesis is rawOffset = 3 with litLen = 0
    (shifted mode returns `history[0]! - 1`), captured by `hshift3`. For all other
    inputs with `rawOffset > 0` and `ValidOffsetHistory`, positivity holds unconditionally.

    This is the single theorem downstream proofs (e.g. `executeSequences` loop
    invariants) should use, avoiding case splits on litLen and rawOffset at each
    loop iteration. -/
theorem resolveOffset_positive_all (rawOffset : Nat) (history : Array Nat) (litLen : Nat)
    (hraw : rawOffset > 0) (hvalid : ValidOffsetHistory history)
    (hshift3 : litLen = 0 ∧ rawOffset = 3 → history[0]! ≥ 2) :
    (resolveOffset rawOffset history litLen).1 > 0 := by
  by_cases hlit : litLen > 0
  · exact resolveOffset_positive_litLen_pos rawOffset history litLen hraw hvalid hlit
  · -- litLen = 0
    have hlit0 : litLen = 0 := by omega
    subst hlit0
    by_cases hle : rawOffset ≤ 2
    · exact resolveOffset_positive_shifted12 rawOffset history hraw hle hvalid
    · by_cases heq3 : rawOffset = 3
      · -- rawOffset = 3, litLen = 0: resolved offset = history[0]! - 1
        have h02 := hshift3 ⟨rfl, heq3⟩
        rw [heq3]
        have := (resolveOffset_shifted3_val history hvalid.1).1
        rw [this]
        omega
      · -- rawOffset > 3
        have : rawOffset > 3 := by omega
        exact resolveOffset_positive_large rawOffset history 0 this

/-- The initial offset history `#[1, 4, 8]` is valid. -/
theorem initial_history_valid : ValidOffsetHistory #[1, 4, 8] := by decide

end Zstd.Spec.Sequence
