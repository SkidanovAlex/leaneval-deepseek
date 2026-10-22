import Mathlib
import Submission.Work.ANALYTIC.CechPt.CechLevels
import Submission.Work.ANALYTIC.CechPt.powMulSumOfDigitsTerm
import Submission.Work.ANALYTIC.CechPt.ofDigits_eq_of_truncOf_close

/-!
# Truncation bounds for binary expansions

This module proves `Work.ANALYTIC.CechPt.ofDigitsTruncBound`, the numerical input to the
construction of the level structure on the Čech nerve terms of the Cantor set.

The two facts are:

* `2^(n+1) * ofDigits d = truncOf n d + θ` with `θ = ofDigits (tail) ∈ [0,1]`, i.e. `truncOf n d`
  is the level-`n` truncation of the binary expansion of `ofDigits d`;
* hence `|ofDigits d - ofDigits e| ≤ 2/2^(m+1)` for every `m` as soon as the truncations of `d`
  and `e` differ by at most one at each level, so `ofDigits d = ofDigits e`.

The second fact is exactly the hypothesis `hclose` threaded through
`Work.ANALYTIC.CechPt.exists_cechTerm_of_compat`: it says that the level-`n` dyadic approximation
determines the point of the Cantor set up to the ambiguity of `0.0111…= 0.1000…`, which is
precisely what "tuples of points of diameter ≤ 1" allows.
-/

open Finset

noncomputable section

namespace Work.ANALYTIC.CechPt

/-- The scaling identity `2^(n+1) * ofDigits d = truncOf n d + θ` with `0 ≤ θ ≤ 1`, where `θ` is
the binary expansion of the tail of the digit sequence `d`. -/
theorem exists_ofDigits_truncOf_decomp (n : ℕ) (d : ℕ → Fin 2) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      (2 : ℝ) ^ (n + 1) * Real.ofDigits d = (truncOf n d : ℝ) + θ := by
  refine ⟨Real.ofDigits (fun i => d (i + (n + 1))), Real.ofDigits_nonneg _,
    Real.ofDigits_le_one _, ?_⟩
  have hkey := Real.ofDigits_eq_sum_add_ofDigits d (n + 1)
  have hcast : (↑(2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [hkey, mul_add, ← mul_assoc, hcast,
    mul_inv_cancel₀ (by positivity : (2 : ℝ) ^ (n + 1) ≠ 0), one_mul, powMulSumOfDigitsTerm]

theorem ofDigitsTruncBound (n : ℕ) (d e : ℕ → Fin 2) :
    (∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      (2 : ℝ) ^ (n + 1) * Real.ofDigits d = (Work.ANALYTIC.CechPt.truncOf n d : ℝ) + θ) ∧
    ((∀ m : ℕ, Work.ANALYTIC.CechPt.truncOf m d ≤ Work.ANALYTIC.CechPt.truncOf m e + 1) →
      (∀ m : ℕ, Work.ANALYTIC.CechPt.truncOf m e ≤ Work.ANALYTIC.CechPt.truncOf m d + 1) →
      Real.ofDigits d = Real.ofDigits e) := by
  refine ⟨exists_ofDigits_truncOf_decomp n d, ?_⟩
  intro h h'
  exact ofDigits_eq_of_truncOf_close d e (Real.ofDigits d) (Real.ofDigits e) h h'
    (fun m => by
      obtain ⟨θ, h0, h1, hθ⟩ := exists_ofDigits_truncOf_decomp m d
      exact ⟨by linarith, by linarith⟩)
    (fun m => by
      obtain ⟨θ, h0, h1, hθ⟩ := exists_ofDigits_truncOf_decomp m e
      exact ⟨by linarith, by linarith⟩)

end Work.ANALYTIC.CechPt
