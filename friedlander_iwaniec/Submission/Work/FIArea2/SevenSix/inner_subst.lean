import Mathlib

namespace Work.FIArea2.SevenSix

-- The inner substitution `s = r*w` (for fixed `r > 0`) in the FI (7.6) computation:
-- `r² - 2γrs + s² = r²(w² - 2γw + 1)` and `√(rs) = r√w`, `ds = r dw`.
-- Intended for arbitrary real `f` (unconditional Bochner-integral identity).
theorem inner_subst (f : ℝ → ℝ) (γ r : ℝ) (hr : 0 < r) :
    ∫ s in Set.Ioi 0, f (r ^ 2 - 2 * γ * r * s + s ^ 2) / Real.sqrt (r * s)
      = ∫ w in Set.Ioi 0, f (r ^ 2 * (w ^ 2 - 2 * γ * w + 1)) / Real.sqrt w := by
  have hr0 : r ≠ 0 := hr.ne'
  -- Pointwise identity after the substitution `s = r*w`: the numerator factors as
  -- `r²(w² - 2γw + 1)` and `√(r·rw) = √(r²w) = r√w`.
  have hpt : ∀ w, f (r ^ 2 - 2 * γ * r * (r * w) + (r * w) ^ 2) / Real.sqrt (r * (r * w))
      = r⁻¹ * (f (r ^ 2 * (w ^ 2 - 2 * γ * w + 1)) / Real.sqrt w) := by
    intro w
    have hnum : r ^ 2 - 2 * γ * r * (r * w) + (r * w) ^ 2
        = r ^ 2 * (w ^ 2 - 2 * γ * w + 1) := by ring
    have hsq : Real.sqrt (r * (r * w)) = r * Real.sqrt w := by
      have h1 : r * (r * w) = r ^ 2 * w := by ring
      rw [h1, Real.sqrt_mul (by positivity), Real.sqrt_sq hr.le]
    rw [hnum, hsq, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
    ring
  -- The scaling substitution on `(0,∞)`: `∫_{x>0} F(r x) dx = r⁻¹ ∫_{s>0} F(s) ds`.
  have hA : ∫ x in Set.Ioi 0, f (r ^ 2 - 2 * γ * r * (r * x) + (r * x) ^ 2) / Real.sqrt (r * (r * x))
      = r⁻¹ * ∫ s in Set.Ioi 0, f (r ^ 2 - 2 * γ * r * s + s ^ 2) / Real.sqrt (r * s) := by
    have h := MeasureTheory.integral_comp_mul_left_Ioi
      (fun s : ℝ => f (r ^ 2 - 2 * γ * r * s + s ^ 2) / Real.sqrt (r * s)) 0 hr
    simpa only [mul_zero, smul_eq_mul] using h
  -- Rewrite the substituted integrand using the pointwise identity, then pull out `r⁻¹`.
  have hB : ∫ x in Set.Ioi 0, f (r ^ 2 - 2 * γ * r * (r * x) + (r * x) ^ 2) / Real.sqrt (r * (r * x))
      = r⁻¹ * ∫ w in Set.Ioi 0, f (r ^ 2 * (w ^ 2 - 2 * γ * w + 1)) / Real.sqrt w := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact MeasureTheory.integral_const_mul r⁻¹
      (fun w => f (r ^ 2 * (w ^ 2 - 2 * γ * w + 1)) / Real.sqrt w)
  have hfin : r⁻¹ * (∫ s in Set.Ioi 0, f (r ^ 2 - 2 * γ * r * s + s ^ 2) / Real.sqrt (r * s))
      = r⁻¹ * (∫ w in Set.Ioi 0, f (r ^ 2 * (w ^ 2 - 2 * γ * w + 1)) / Real.sqrt w) := by
    rw [← hA, hB]
  exact mul_left_cancel₀ (inv_ne_zero hr0) hfin

end Work.FIArea2.SevenSix
