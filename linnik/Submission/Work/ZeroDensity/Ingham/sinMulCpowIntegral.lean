import Mathlib

namespace Work.ZeroDensity.Ingham

open Set MeasureTheory intervalIntegral in
theorem sinMulCpowIntegral {c : ℂ} (hc : 0 < c.re) {A : ℝ} (hA : 0 < A) :
    c * (∫ v in Set.Ioc 0 A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (c - 1)) =
      ((Real.sin A : ℝ) : ℂ) * (A : ℂ) ^ c -
        ∫ v in Set.Ioc 0 A, ((Real.cos v : ℝ) : ℂ) * (v : ℂ) ^ c := by
  have hc_ne : c ≠ 0 := by rintro rfl; simp at hc
  rw [← intervalIntegral.integral_of_le hA.le, ← intervalIntegral.integral_of_le hA.le]
  -- Rewrite the left-hand side so that `c` sits inside the cpow-derivative factor.
  have hL : c * ∫ v in (0 : ℝ)..A, ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (c - 1)
      = ∫ v in (0 : ℝ)..A, ((Real.sin v : ℝ) : ℂ) * (c * (v : ℂ) ^ (c - 1)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  rw [hL]
  -- Integration by parts with `u = sin`, `v = (·)^c`, `u' = cos`, `v' = c*(·)^(c-1)`.
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun y : ℝ => ((Real.sin y : ℝ) : ℂ)) (v := fun y : ℝ => (y : ℂ) ^ c)
    (u' := fun y : ℝ => ((Real.cos y : ℝ) : ℂ)) (v' := fun y : ℝ => c * (y : ℂ) ^ (c - 1))
    (by exact (Complex.continuous_ofReal.comp Real.continuous_sin).continuousOn)
    (by exact (Complex.continuous_ofReal_cpow_const hc).continuousOn)
    (by intro x hx; exact (Real.hasDerivAt_sin x).ofReal_comp)
    (by intro x hx
        rw [min_eq_left hA.le, max_eq_right hA.le] at hx
        exact hasDerivAt_ofReal_cpow_const hx.1.ne' hc_ne)
    (by exact (Complex.continuous_ofReal.comp Real.continuous_cos).intervalIntegrable 0 A)
    (by exact (intervalIntegrable_cpow' (by rw [Complex.sub_re, Complex.one_re]; linarith)).const_mul c)
  rw [hibp]
  simp

end Work.ZeroDensity.Ingham
