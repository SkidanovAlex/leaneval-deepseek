import Mathlib

open MeasureTheory
open scoped Real Topology

set_option autoImplicit false

namespace Commons.NumberTheory.Linnik

/-- For every `c > 0` and all large `x`, `log (log x) ≤ c x`.  (Used to turn the rectangle bound
`L(1-β) ≤ loglog L/3` into the hypothesis `L(1-β) ≤ (δ/2)L` of `gt_half_delta_of_far`.) -/
theorem exists_loglog_le_mul {c : ℝ} (hc : 0 < c) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → Real.log (Real.log x) ≤ c * x := by
  have hc4 : 0 < 4 / c^2 := by positivity
  refine ⟨max (Real.exp 1) (max 1 (4 / c^2)), ?_, ?_⟩
  · have h1 : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2 : (0:ℝ) ≤ 4 / c^2 := hc4.le
    have h3 : (0:ℝ) ≤ 1 := zero_le_one
    have h4 : (1:ℝ) ≤ max (1:ℝ) (4 / c^2) := le_max_left _ _
    have h5 : max (1:ℝ) (4 / c^2) ≤ max (Real.exp 1) (max 1 (4 / c^2)) := le_max_right _ _
    linarith [h1, h4, h5]
  · intro x hx
    have hxe : Real.exp 1 ≤ x := le_trans (le_max_left _ _) hx
    have hx1 : (1:ℝ) ≤ x := le_trans (Real.one_le_exp zero_le_one) hxe
    have hx4 : 4 / c^2 ≤ x :=
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)
    have hlogx1 : 1 ≤ Real.log x := by
      calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) hxe
    have hlogcl : Real.log (Real.log x) ≤ Real.log x := by
      have h := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hlogx1)
      linarith
    have hsqrt : Real.log x ≤ 2 * Real.sqrt x := by
      have h := Real.log_le_rpow_div (x := x) (by linarith : (0:ℝ) ≤ x)
        (by norm_num : (0:ℝ) < 1/2)
      rw [← Real.sqrt_eq_rpow] at h
      linarith
    have hs : 2 / c ≤ Real.sqrt x := by
      have hsqx : (2/c)^2 ≤ x := by
        rw [div_pow, show (2:ℝ)^2 = 4 by norm_num]
        rw [div_le_iff₀ (by positivity : (0:ℝ) < c^2)] at hx4
        rw [div_le_iff₀ (by positivity : (0:ℝ) < c^2)]
        linarith
      have h1 : Real.sqrt ((2/c)^2) ≤ Real.sqrt x := Real.sqrt_le_sqrt hsqx
      rwa [Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 / c)] at h1
    have hfin : 2 * Real.sqrt x ≤ c * x := by
      have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith : (0:ℝ) ≤ x)
      have h2 : (2:ℝ) ≤ c * Real.sqrt x := by
        have hh := mul_le_mul_of_nonneg_left hs (le_of_lt hc)
        rw [mul_div_cancel₀ _ (ne_of_gt hc)] at hh
        exact hh
      calc 2 * Real.sqrt x ≤ (c * Real.sqrt x) * Real.sqrt x :=
            mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg x)
        _ = c * x := by rw [mul_assoc, hsq]
    linarith [hlogcl, hsqrt, hfin]

end Commons.NumberTheory.Linnik
