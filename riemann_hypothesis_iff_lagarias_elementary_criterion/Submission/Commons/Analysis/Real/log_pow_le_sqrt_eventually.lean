import Mathlib
import Submission.Commons.Analysis.Real.exists_pow_log_div_sqrt_le

namespace Commons.Analysis.Real

theorem log_pow_le_sqrt_eventually (k : ℕ) (C : ℝ) (hC : 0 < C) :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → C * (Real.log x) ^ k ≤ Real.sqrt x := by
  obtain ⟨Y, _hY1, hY⟩ := exists_pow_log_div_sqrt_le k (show (0 : ℝ) < 1 / C by positivity)
  refine ⟨max Y 1, fun x hx => ?_⟩
  have hxY : Y ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hx1)
  have h := hY x hxY
  have hc : C * (1 / C) = 1 := by field_simp
  have hmul : C * ((Real.log x) ^ k / Real.sqrt x) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left h hC.le
    rwa [hc] at this
  have hdiv : C * (Real.log x) ^ k / Real.sqrt x ≤ 1 := by
    rwa [mul_div_assoc]
  have := (div_le_iff₀ hsqrt_pos).mp hdiv
  simpa using this

end Commons.Analysis.Real
