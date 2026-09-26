import Mathlib
import Submission.Work.Smooth.SphereJordan.Caratheodory.InverseAnalytic

/-!
# The Jacobian determinant of a holomorphic map, and the area formula

The analytic input of the boundary-correspondence proof of Carathéodory's theorem (see the Wikipedia
/Garnett–Marshall proof) is the *length–area* (or "energy = area") estimate: for a holomorphic
injection `f` on `U`,

  `∫∫_U ‖f'‖² = Area (f '' U)`.

Here we prove the two ingredients:

* `abs_det_fderiv_eq_norm_deriv_sq` — the real Jacobian determinant of a holomorphic function is
  `‖deriv f z‖²`.  This reduces, through `Algebra.leftMulMatrix_complex`/`Algebra.norm_complex_apply`,
  to Mathlib's computation of the determinant of multiplication by a complex number
  (`Algebra.norm_eq_matrix_det`);

* `lintegral_normSq_deriv_eq_volume` — the change-of-variables formula
  (`MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`) applied with the constant
  function `1` turns this into the equality of the "Dirichlet energy" with the area.
-/

noncomputable section

open Set Metric Filter MeasureTheory

open scoped Topology ENNReal

namespace Work.Smooth.SphereJordan.Caratheodory

theorem lmul_coe (c : ℂ) : (Algebra.lmul ℝ ℂ c : ℂ →ₗ[ℝ] ℂ) = LinearMap.mul ℝ ℂ c :=
  congrFun Algebra.coe_lmul_eq_mul c

theorem lmul_apply_complex (c w : ℂ) : (Algebra.lmul ℝ ℂ c) w = c * w := by
  rw [lmul_coe, LinearMap.mul_apply']

theorem det_lmul_complex (c : ℂ) : LinearMap.det (Algebra.lmul ℝ ℂ c) = Complex.normSq c := by
  rw [← Algebra.norm_apply (R := ℝ) (S := ℂ) c, Algebra.norm_complex_apply]

/-- For a function holomorphic at `z`, the real derivative is multiplication by `deriv f z`. -/
theorem fderiv_real_eq_lmul {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    (fderiv ℝ f z : ℂ →ₗ[ℝ] ℂ) = Algebra.lmul ℝ ℂ (deriv f z) := by
  ext w
  rw [hf.fderiv_restrictScalars ℝ]
  show (fderiv ℂ f z) w = (Algebra.lmul ℝ ℂ (deriv f z)) w
  have h1 : (fderiv ℂ f z) w = w * deriv f z := by
    rw [show w = w • (1 : ℂ) by simp, ContinuousLinearMap.map_smul]
    simp [smul_eq_mul]
  rw [h1, lmul_apply_complex, mul_comm]

/-- The (real) Jacobian determinant of a holomorphic function is the square of the modulus of its
complex derivative. -/
theorem abs_det_fderiv_eq_norm_deriv_sq {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    |(fderiv ℝ f z).det| = ‖deriv f z‖ ^ 2 := by
  have h : (fderiv ℝ f z).det = Complex.normSq (deriv f z) := by
    rw [show (fderiv ℝ f z).det = LinearMap.det (fderiv ℝ f z : ℂ →ₗ[ℝ] ℂ) from rfl,
      fderiv_real_eq_lmul hf, det_lmul_complex]
  rw [h, Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]

/-- **Energy = area for an injective holomorphic map**: if `f` is holomorphic and injective on the
open set `U ⊆ ℂ`, the integral of `‖f'‖²` over `U` equals the area of the image. -/
theorem lintegral_normSq_deriv_eq_volume {U : Set ℂ} (hUo : IsOpen U) {f : ℂ → ℂ}
    (hinj : InjOn f U) (hfd : ∀ z ∈ U, DifferentiableAt ℂ f z) :
    ∫⁻ z in U, ENNReal.ofReal (‖deriv f z‖ ^ 2) ∂volume = volume (f '' U) := by
  have hmeas : MeasurableSet U := hUo.measurableSet
  have hderiv : ∀ x ∈ U, HasFDerivWithinAt f (fderiv ℝ f x) U x := by
    intro x hx
    have h1 : HasFDerivAt f (fderiv ℝ f x) x := by
      rw [(hfd x hx).fderiv_restrictScalars ℝ]
      exact (hfd x hx).hasFDerivAt.restrictScalars ℝ
    exact h1.hasFDerivWithinAt
  have hmain : volume (f '' U) = ∫⁻ z in U, ENNReal.ofReal |(fderiv ℝ f z).det| ∂volume := by
    have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul (μ := volume)
      (f' := fun x => fderiv ℝ f x) hmeas hderiv hinj (fun _ => 1)
    simpa only [lintegral_one, Measure.restrict_apply_univ, mul_one] using h
  rw [hmain]
  refine setLIntegral_congr_fun hmeas fun x hx => ?_
  rw [abs_det_fderiv_eq_norm_deriv_sq (hfd x hx)]

end Work.Smooth.SphereJordan.Caratheodory
