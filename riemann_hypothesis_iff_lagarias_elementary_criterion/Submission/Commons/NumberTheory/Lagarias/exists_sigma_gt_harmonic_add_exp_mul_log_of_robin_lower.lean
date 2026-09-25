import Mathlib
import Submission.Commons.NumberTheory.Lagarias.harmonic_add_exp_mul_log_le
import Submission.Commons.NumberTheory.Lagarias.eventually_upper_lt_robin_lower

namespace Commons.NumberTheory.Lagarias

theorem exists_sigma_gt_harmonic_add_exp_mul_log_of_robin_lower (h : ∃ β : ℝ, 0 < β ∧ β < 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧ Filter.Frequently (fun n : ℕ => ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≥ Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) + C * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ β) Filter.atTop) : ∃ n : ℕ, 0 < n ∧ (harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) < ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) := by
  rcases h with ⟨β, hβ0, hβ1, C, hC, hfreq⟩
  have hev := eventually_upper_lt_robin_lower hβ0 hβ1 hC
  have hev1 : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ n := Filter.eventually_ge_atTop 1
  have hQ : ∀ᶠ n : ℕ in Filter.atTop,
      ((harmonic n : ℝ) + Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ) <
        Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) +
          C * (n : ℝ) * Real.log (Real.log (n : ℝ)) / (Real.log (n : ℝ)) ^ β) ∧ 1 ≤ n :=
    hev.and hev1
  obtain ⟨n, hσ, hlt, hn1⟩ := (hfreq.and_eventually hQ).exists
  refine ⟨n, hn1, ?_⟩
  exact lt_of_lt_of_le hlt hσ

end Commons.NumberTheory.Lagarias
