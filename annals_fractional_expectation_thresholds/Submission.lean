/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/

import Mathlib.Probability.Distributions.SetBernoulli
import Submission.Helpers
import Submission.Prob
import Submission.Monotone
import Submission.Mono2
import Submission.Pc
import Submission.Core
import ChallengeDeps
/-!
# Main Statement from Thresholds versus fractional expectation-thresholds

We formalise the statement of the main result from K. Frankston, J. Kahn, B. Narayanan, and J. Park,
`Thresholds versus fractional expectation-thresholds`, Annals of Math, 194 (2) 2021.
-/


namespace Submission

open _root_.FractionalExpectationThresholds
set_option autoImplicit false

namespace FractionalExpectationThresholds

open ProbabilityTheory unitInterval Set

open scoped NNReal

/-- The constant `K` in Theorem 1.1. -/
noncomputable def K : ℝ := Submission.FET.CoreK

/--
Statement of Theorem 1.1:

There exists a universal constant `K` such that for any finite set `X` and any increasing
collection of sets `𝓕` such that `l(𝓕)` is at least `2`,

`p_c(𝓕) ≤ K * q_f(𝓕) * log l(𝓕)`.

Note: The assumption that `l(𝓕)` is at least `2` is not explicitly in the paper but is needed
because if `l(𝓕) = 1` then `Real.log (l 𝓕) = 0`, but `p_c 𝓕 ∈ (0,1)` (so the inequality clearly
cannot hold).
-/
theorem theorem_1_1 (X : Type*) [Fintype X] (𝓕 : Set (Set X)) (h𝓕 : IsUpperSet 𝓕)
    (hl𝓕 : 2 ≤ l 𝓕) : p_c 𝓕 ≤ K * q_f 𝓕 * Real.log (l 𝓕) := by
  classical
  let q : ℝ := (q_f 𝓕 : ℝ)
  let r : ℝ := K * q * Real.log (l 𝓕)
  by_cases h1 : 1 ≤ r
  · -- p_c ≤ 1 ≤ r
    have hpc : (p_c 𝓕 : ℝ) ≤ 1 := Submission.FET.p_c_le_one (X := X) (𝓕 := 𝓕)
    exact le_trans hpc h1
  · -- r < 1
    have hrle : r ≤ 1 := le_of_not_ge h1
    have hq0 : 0 ≤ q := (q_f 𝓕).2.1
    have hK0 : 0 ≤ K := by
      norm_num [K, Submission.FET.CoreK, Submission.FET.MTK]
    have hll : (1 : ℝ) ≤ (l 𝓕 : ℝ) := by
      have : (1 : ℕ) ≤ l 𝓕 := by omega
      exact_mod_cast this
    have hlog0 : 0 ≤ Real.log (l 𝓕) := Real.log_nonneg hll
    have hr0 : 0 ≤ r := by
      unfold r
      exact mul_nonneg (mul_nonneg hK0 hq0) hlog0
    let pstar : I := ⟨r, hr0, hrle⟩
    have hpval : (pstar : ℝ) = Submission.FET.CoreK * (q_f 𝓕 : ℝ) * Real.log (l 𝓕) := by
      simp [pstar, r, q, K]
    have hcore := Submission.FET.core_estimate (X := X) (𝓕 := 𝓕) h𝓕 hl𝓕 (pstar := pstar) hpval
      pstar.2.2
    have hgt : (1 / 2 : ℝ) < Submission.FET.mu pstar 𝓕 := by
      have : (3 / 4 : ℝ) ≤ Submission.FET.mu pstar 𝓕 := hcore
      norm_num
      linarith
    have hpc := Submission.FET.p_c_le_of_mu_gt_half (X := X) (𝓕 := 𝓕) h𝓕 pstar hgt
    -- hpc : (p_c 𝓕 : ℝ) ≤ (pstar : ℝ) = r = K q log l
    rw [hpval] at hpc
    simpa [K, q] using hpc

end FractionalExpectationThresholds

end Submission
