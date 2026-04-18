import Zstd.Spec.Fse.Basic

/-!
# `decodeFseSymbolsWF` output-size correctness

Shows that on success `decodeFseSymbolsWF` produces exactly `count`
symbols (when `count > 0`), via an inner-loop size invariant. -/

namespace Zstd.Spec.Fse

open Zstd.Native (FseTable BackwardBitReader)

/-! ## `decodeFseSymbolsWF` output size -/

open Zstd.Native in
/-- The inner loop of `decodeFseSymbolsWF` produces exactly
    `acc.size + remaining` elements on success. -/
theorem decodeFseSymbolsWF_loop_size
    {table : FseTable} {br br' : BackwardBitReader}
    {state remaining : Nat}
    {acc result : Array UInt8}
    (h : decodeFseSymbolsWF.loop table br state remaining acc
           = .ok (result, br')) :
    result.size = acc.size + remaining := by
  induction remaining generalizing br state acc with
  | zero =>
    simp only [decodeFseSymbolsWF.loop, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    omega
  | succ n ih =>
    simp only [decodeFseSymbolsWF.loop] at h
    split at h
    · exact nomatch h
    · simp only [beq_iff_eq] at h
      split at h
      · -- n = 0, last symbol
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        simp only [Array.size_push]
        omega
      · -- n > 0, recursive case
        simp only [bind, Except.bind] at h
        split at h
        · exact nomatch h
        · rw [ih h]
          simp only [Array.size_push]
          omega

open Zstd.Native in
/-- When `decodeFseSymbolsWF` succeeds with `count > 0`, the output array
    has exactly `count` elements. -/
theorem decodeFseSymbolsWF_size
    {table : FseTable} {br br' : BackwardBitReader}
    {count : Nat} {result : Array UInt8}
    (h : decodeFseSymbolsWF table br count = .ok (result, br'))
    (hcount : 0 < count) :
    result.size = count := by
  simp only [decodeFseSymbolsWF, beq_iff_eq] at h
  split at h
  · omega
  · simp only [bind, Except.bind] at h
    cases hrb : br.readBits table.accuracyLog with
    | error e => simp only [hrb] at h; exact nomatch h
    | ok val =>
      simp only [hrb] at h
      have := decodeFseSymbolsWF_loop_size h
      simp only [Array.size_empty] at this; omega

end Zstd.Spec.Fse
