import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory

/-- The derivative of the standard Gaussian weight `x ↦ exp (-(x^2/2))`. -/
lemma deriv_gaussianWeight (x : ℝ) :
    deriv (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) x = -x * Real.exp (-(x ^ 2 / 2)) := by
  rw [deriv_exp (by simp)]
  simp [mul_comm]

/-- `HasDerivAt` form of the derivative of the standard Gaussian weight. -/
lemma hasDerivAt_gaussianWeight (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) (-x * Real.exp (-(x ^ 2 / 2))) x := by
  have hdiff : DifferentiableAt ℝ (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) x := by fun_prop
  rw [← deriv_gaussianWeight x]
  exact hdiff.hasDerivAt

theorem gaussian_integration_by_parts (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    (∫ x : ℝ, deriv f x * Real.exp (-(x ^ 2 / 2)))
      = ∫ x : ℝ, x * f x * Real.exp (-(x ^ 2 / 2)) := by
  let w : ℝ → ℝ := fun x => Real.exp (-(x ^ 2 / 2))
  let w' : ℝ → ℝ := fun x => -x * Real.exp (-(x ^ 2 / 2))
  have hf_cont : Continuous f := hf.continuous
  have hderiv_cont : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hf_diff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hu : ∀ x ∈ tsupport w, HasDerivAt f (deriv f x) x := fun x _ => (hf_diff x).hasDerivAt
  have hv : ∀ x ∈ tsupport f, HasDerivAt w (w' x) x := fun x _ => hasDerivAt_gaussianWeight x
  have huv' : Integrable (f * w') := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hf_cont.mul (by fun_prop)
    · exact hc.mul_right
  have hu'v : Integrable (deriv f * w) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hderiv_cont.mul (by fun_prop)
    · exact hc.deriv.mul_right
  have huv : Integrable (f * w) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hf_cont.mul (by fun_prop)
    · exact hc.mul_right
  have h := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (v := w) (u' := deriv f) (v' := w') hu hv huv' hu'v huv
  have hL : (∫ x : ℝ, f x * w' x) = - ∫ x : ℝ, x * f x * w x := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    simp only [w, w']
    ring
  rw [hL] at h
  simpa only [w] using (neg_inj.mp h).symm

end Commons.Analysis.GaussianMeasure