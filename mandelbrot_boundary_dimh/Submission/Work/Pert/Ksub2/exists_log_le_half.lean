import Mathlib

namespace Work.Pert.Ksub2

/-- For every real `C` there is `R` such that `C (1 + log x) ≤ x / 2` for all `x ≥ R`:
the linear term eventually dominates the logarithm. -/
theorem exists_log_le_half (C : ℝ) : ∃ R : ℝ, ∀ x : ℝ, R ≤ x → C * (1 + Real.log x) ≤ x / 2 := by
  refine ⟨max 1 (36 * C ^ 2), fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hx36 : 36 * C ^ 2 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 ≤ x := le_trans zero_le_one hx1
  by_cases hC : C ≤ 0
  · have h1 : 0 ≤ 1 + Real.log x := by
      have := Real.log_nonneg hx1
      linarith
    have := mul_nonpos_of_nonpos_of_nonneg hC h1
    linarith
  · have hCpos : 0 < C := not_le.mp hC
    -- `log x ≤ 2 √x`
    have hlog : Real.log x ≤ 2 * Real.sqrt x := by
      have h := Real.log_le_rpow_div hx0 (show (0:ℝ) < 1/2 by norm_num)
      rw [← Real.sqrt_eq_rpow] at h
      linarith
    -- `6 C ≤ √x`
    have h6C : 6 * C ≤ Real.sqrt x := by
      have h1 : Real.sqrt ((6 * C) ^ 2) ≤ Real.sqrt x := Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_sq_eq_abs, abs_of_pos (by linarith : (0:ℝ) < 6 * C)] at h1
    have hsqrt1 : 1 ≤ Real.sqrt x := (Real.one_le_sqrt).2 hx1
    have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
    have key : 1 + Real.log x ≤ 3 * Real.sqrt x := by linarith
    have h2 : C * (1 + Real.log x) ≤ C * (3 * Real.sqrt x) :=
      mul_le_mul_of_nonneg_left key (le_of_lt hCpos)
    have h3 : C * (3 * Real.sqrt x) ≤ x / 2 := by nlinarith [h6C, hsq, hCpos]
    linarith

end Work.Pert.Ksub2
