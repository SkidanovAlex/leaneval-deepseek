import Mathlib

namespace Work.RPB1a.Caratheodory.Area

open Complex Set Metric MeasureTheory
open scoped ENNReal Real Topology

/-- The (absolute value of the) Jacobian determinant of a holomorphic map at a point equals the
square of the modulus of its complex derivative. This is the Cauchy–Riemann identity
`det (fderiv ℝ f z) = |f'(z)|²`, expressed through `Complex.normSq`. -/
lemma abs_det_fderiv_eq (f : ℂ → ℂ) (z : ℂ) (h : DifferentiableAt ℂ f z) :
    |(fderiv ℝ f z).det| = ‖deriv f z‖ ^ 2 := by
  have h1 : fderiv ℝ f z = (ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)).restrictScalars ℝ := by
    rw [h.fderiv_restrictScalars ℝ, h.hasDerivAt.hasFDerivAt.fderiv]
  have h2 : (((ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)).restrictScalars ℝ : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ)
      = Algebra.lmul ℝ ℂ (deriv f z) := by
    ext x
    rw [ContinuousLinearMap.coe_restrictScalars, LinearMap.restrictScalars_apply]
    show (ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)) x = deriv f z * x
    rw [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_comm]
  have h3 : (fderiv ℝ f z).det = LinearMap.det (Algebra.lmul ℝ ℂ (deriv f z)) := by
    rw [h1]
    exact congrArg LinearMap.det h2
  rw [h3, ← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq,
    abs_of_nonneg (sq_nonneg _)]

/-- Finiteness of the Dirichlet integral of an injective holomorphic map with bounded image
(the area formula for a holomorphic injection, used for its finiteness consequence). -/
theorem lintegral_enorm_deriv_sq_ne_top {U : Set ℂ} (hUo : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) (hb : Bornology.IsBounded (f '' U)) :
    ∫⁻ z in U, ‖deriv f z‖ₑ ^ 2 ≠ ⊤ := by
  have hUmeas : MeasurableSet U := hUo.measurableSet
  have hf' : ∀ z ∈ U, HasFDerivWithinAt f (fderiv ℝ f z) U z := fun z hz =>
    (((hf z hz).differentiableAt (hUo.mem_nhds hz)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
  -- Change of variables (area formula) for the real-differentiable injective map `f` on `U`.
  have hcv := MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image (μ := volume) hUmeas hf' hinj
  -- Identify the Dirichlet integrand `‖f'‖ₑ²` with the Jacobian `ofReal |det (fderiv ℝ f)|`.
  have hE : ∫⁻ z in U, ‖deriv f z‖ₑ ^ 2
      = ∫⁻ z in U, ENNReal.ofReal |(fderiv ℝ f z).det| := by
    apply lintegral_congr_ae
    filter_upwards [MeasureTheory.self_mem_ae_restrict hUmeas] with z hz
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), abs_det_fderiv_eq f z
      ((hf z hz).differentiableAt (hUo.mem_nhds hz))]
  rw [hE, hcv]
  exact (Bornology.IsBounded.measure_lt_top hb).ne

end Work.RPB1a.Caratheodory.Area
