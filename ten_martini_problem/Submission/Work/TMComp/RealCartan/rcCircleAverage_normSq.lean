import Mathlib

/-!
# The circle average of the squared norm

For every centre `z : ℂ` and every radius `r : ℝ`, the average of `w ↦ ‖w‖ ^ 2` over the circle
with centre `z` and radius `r` (with respect to the rotation invariant probability measure) equals
`‖z‖ ^ 2 + r ^ 2`.

The proof is a direct computation.  Parametrising the circle as `θ ↦ z + r * exp (θ * I)` one has
`‖z + r * exp (θ * I)‖ ^ 2 = ‖z‖ ^ 2 + r ^ 2 + 2 * r * (z.re * cos θ + z.im * sin θ)`, and the
integrals of `cos` and `sin` over a full period vanish.
-/

namespace Work.TMComp.RealCartan

/-- Expansion of `‖a + b‖ ^ 2` in terms of real and imaginary parts. -/
private lemma norm_sq_add (a b : ℂ) :
    ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * (a.re * b.re + a.im * b.im) := by
  have h : Complex.normSq (a + b) = Complex.normSq a + Complex.normSq b +
      2 * (a.re * b.re + a.im * b.im) := by
    rw [Complex.normSq_add, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  simpa only [Complex.normSq_eq_norm_sq] using h

/-- Pointwise expansion of `‖·‖ ^ 2` on the circle with centre `z` and radius `r`. -/
private lemma norm_sq_circleMap (z : ℂ) (r θ : ℝ) :
    ‖circleMap z r θ‖ ^ 2 =
      (‖z‖ ^ 2 + r ^ 2) + 2 * (z.re * (r * Real.cos θ) + z.im * (r * Real.sin θ)) := by
  have h1 : circleMap z r θ = z + circleMap 0 r θ := by
    simp only [circleMap, zero_add]
  rw [h1, norm_sq_add, norm_circleMap_zero, sq_abs, circleMap_zero_re, circleMap_zero_im]

theorem rcCircleAverage_normSq (z : ℂ) (r : ℝ) :
    Real.circleAverage (fun w : ℂ => ‖w‖ ^ 2) z r = ‖z‖ ^ 2 + r ^ 2 := by
  -- The integrals of `cos` and `sin` over a full period vanish.
  have hcos : ∫ θ in (0 : ℝ)..2 * Real.pi, Real.cos θ = 0 := by simp
  have hsin : ∫ θ in (0 : ℝ)..2 * Real.pi, Real.sin θ = 0 := by simp
  -- Integrability of the three pieces of the integrand.
  have hA : IntervalIntegrable (fun _ : ℝ => (‖z‖ ^ 2 + r ^ 2)) MeasureTheory.volume 0
      (2 * Real.pi) := continuous_const.intervalIntegrable _ _
  have hAB : IntervalIntegrable
      (fun θ : ℝ => (‖z‖ ^ 2 + r ^ 2) + (2 * z.re * r) * Real.cos θ) MeasureTheory.volume 0
      (2 * Real.pi) :=
    (by fun_prop : Continuous fun θ : ℝ => (‖z‖ ^ 2 + r ^ 2) + (2 * z.re * r) * Real.cos θ
      ).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun θ : ℝ => (2 * z.re * r) * Real.cos θ) MeasureTheory.volume 0
      (2 * Real.pi) :=
    (by fun_prop : Continuous fun θ : ℝ => (2 * z.re * r) * Real.cos θ).intervalIntegrable _ _
  have hC : IntervalIntegrable (fun θ : ℝ => (2 * z.im * r) * Real.sin θ) MeasureTheory.volume 0
      (2 * Real.pi) :=
    (by fun_prop : Continuous fun θ : ℝ => (2 * z.im * r) * Real.sin θ).intervalIntegrable _ _
  -- The integral over one period of the squared norm.
  have hInt : (∫ θ in (0 : ℝ)..2 * Real.pi, ‖circleMap z r θ‖ ^ 2) =
      2 * Real.pi * (‖z‖ ^ 2 + r ^ 2) := by
    have hcongr : (∫ θ in (0 : ℝ)..2 * Real.pi, ‖circleMap z r θ‖ ^ 2) =
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          ((‖z‖ ^ 2 + r ^ 2) + (2 * z.re * r) * Real.cos θ + (2 * z.im * r) * Real.sin θ) :=
      intervalIntegral.integral_congr (fun θ _ => by rw [norm_sq_circleMap z r θ]; ring)
    rw [hcongr,
      intervalIntegral.integral_add hAB hC,
      intervalIntegral.integral_add hA hB,
      intervalIntegral.integral_const, smul_eq_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      hcos, hsin]
    ring
  rw [Real.circleAverage_def, smul_eq_mul, hInt,
    inv_mul_cancel_left₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero)]

end Work.TMComp.RealCartan
