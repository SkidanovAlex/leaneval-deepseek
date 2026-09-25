import Mathlib
import Submission.Work.RHContract.Corpus

namespace Work.RHContract.B

open scoped ArithmeticFunction.sigma

/-- The elementary transfer used in the Lagarias-criterion project: if Robin's inequality
`σ(n) ≤ e^γ n log log n` fails infinitely often by an additive relative margin
(`SigmaOscillation`), then it cannot hold for *all* `n ≥ 5041`.

Given a value `n ≥ 5041` at which the oscillation inequality holds, the exponential
`e^γ n log log n` is strictly topped up by the positive term
`C n log log n / (log n)^β`, so Robin's bound is violated at that `n`; and
`Filter.Frequently · atTop` furnishes such `n` arbitrarily large. -/
theorem sigmaOscillation_not_robin_upper (h : Work.RHPlan.SigmaOscillation) :
    ¬ (∀ n : ℕ, 5041 ≤ n →
      ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
        Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ))) := by
  rintro H
  obtain ⟨β, hβpos, hβlt, C, hCpos, hfreq⟩ := h
  -- `Frequently · atTop` on `ℕ` means: witnesses exist above every bound.
  rw [Filter.frequently_atTop] at hfreq
  obtain ⟨n, hn5041, hnP⟩ := hfreq 5041
  have hn_real : (5041 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn5041
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  -- `n ≥ 5041` implies `log n > 1`, hence `log log n > 0`.
  have hexp_lt : Real.exp 1 < (n : ℝ) := by
    have h3 : Real.exp 1 < (5041 : ℝ) := by
      have h := Real.exp_one_lt_three
      have h4 : (3 : ℝ) < 5041 := by norm_num
      linarith
    linarith
  have hlog_gt1 : (1 : ℝ) < Real.log (n : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hn_pos]
    exact hexp_lt
  have hloglog_pos : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos hlog_gt1
  have hlog_pos : 0 < Real.log (n : ℝ) := by linarith
  -- The additive correction in `SigmaOscillation` is strictly positive at this `n`.
  have htpos : 0 < C * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ β := by
    apply div_pos _ (Real.rpow_pos_of_pos hlog_pos β)
    positivity
  have hH := H n hn5041
  linarith

end Work.RHContract.B
