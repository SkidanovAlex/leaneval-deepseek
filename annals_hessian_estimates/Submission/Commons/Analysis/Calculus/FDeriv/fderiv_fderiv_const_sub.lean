import Mathlib

namespace Commons.Analysis.Calculus.FDeriv

open MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace Convolution

/-- The second derivative of `w ↦ k (y - w)` equals the second derivative of `k` at `y - w`.
The two reflections in `w ↦ y - w` cancel in the second derivative. -/
theorem fderiv_fderiv_const_sub_general {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : E → ℝ) (y z : E) (hk : ContDiff ℝ 2 k) :
    fderiv ℝ (fderiv ℝ (fun w => k (y - w))) z = fderiv ℝ (fderiv ℝ k) (y - z) := by
  let φ : E → E := fun w => y - w
  have hφ_diff : ∀ w, DifferentiableAt ℝ φ w := by
    intro w
    fun_prop
  have hφ_deriv : ∀ w, fderiv ℝ φ w = -ContinuousLinearMap.id ℝ E := by
    intro w
    change fderiv ℝ (fun w : E => y - w) w = -ContinuousLinearMap.id ℝ E
    rw [show (fun w : E => y - w) = (fun w : E => y - id w) from rfl, fderiv_const_sub]
    rw [fderiv_id]
  have hk_diff : Differentiable ℝ k := hk.differentiable (by norm_num)
  have hA_diff : DifferentiableAt ℝ (fderiv ℝ k) (y - z) := by
    have h : ContDiff ℝ 1 (fderiv ℝ k) := hk.fderiv_right (m := 1) (by norm_num)
    exact h.contDiffAt.differentiableAt (by norm_num)
  have hF : fderiv ℝ (fun w : E => k (y - w)) = fun w => - fderiv ℝ k (y - w) := by
    funext w
    rw [fderiv_fun_comp w (hk_diff.differentiableAt) (hφ_diff w)]
    rw [hφ_deriv w]
    simp only [φ, ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id]
  have hB : fderiv ℝ (fun w : E => fderiv ℝ k (y - w)) z
      = - fderiv ℝ (fderiv ℝ k) (y - z) := by
    rw [fderiv_fun_comp z hA_diff (hφ_diff z)]
    rw [hφ_deriv z]
    simp only [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id]
  rw [hF, fderiv_fun_neg, hB]
  simp

open MeasureTheory Metric Set Filter Function in
open scoped BigOperators ENNReal Topology RealInnerProductSpace InnerProductSpace Convolution in
theorem fderiv_fderiv_const_sub {n : ℕ} (k : EuclideanSpace ℝ (Fin n) → ℝ)
    (y z : EuclideanSpace ℝ (Fin n)) (hk : ContDiff ℝ 2 k) :
    fderiv ℝ (fderiv ℝ (fun z => k (y - z))) z = fderiv ℝ (fderiv ℝ k) (y - z) := by
  exact fderiv_fderiv_const_sub_general k y z hk

end Commons.Analysis.Calculus.FDeriv
