import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Calculus

open scoped Topology

namespace Commons.Analysis.InnerProductSpace

/-- The Fréchet derivative of the norm on a real inner product space at a nonzero point. -/
theorem hasFDerivAt_norm_ne_zero {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {x : F} (hx : x ≠ 0) :
    HasFDerivAt (fun y : F => ‖y‖) ((‖x‖)⁻¹ • (innerSL ℝ x)) x := by
  have hx2 : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hg : HasFDerivAt (fun y : F => ‖y‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h := hg.sqrt hx2
  have hfun : (fun y : F => ‖y‖) =ᶠ[𝓝 x] (fun y : F => √(‖y‖ ^ 2)) :=
    Filter.Eventually.of_forall (fun y => (Real.sqrt_sq (norm_nonneg y)).symm)
  have h1 : HasFDerivAt (fun y : F => ‖y‖) ((1 / (2 * √(‖x‖ ^ 2))) • (2 • innerSL ℝ x)) x :=
    h.congr_of_eventuallyEq hfun
  rw [Real.sqrt_sq (norm_nonneg x)] at h1
  refine h1.congr_fderiv ?_
  ext v
  simp only [smul_apply, smul_eq_mul, coe_innerSL_apply]
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp
  ring

theorem fderiv_norm_single
    {n : ℕ} (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖) x (EuclideanSpace.single i 1) = x i / ‖x‖ := by
  rw [(hasFDerivAt_norm_ne_zero hx).fderiv]
  rw [smul_apply, smul_eq_mul]
  rw [innerSL_apply_apply, EuclideanSpace.inner_single_right, div_eq_inv_mul]
  simp [mul_comm]

end Commons.Analysis.InnerProductSpace