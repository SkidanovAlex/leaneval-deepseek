import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.BoseB1Cube

/-- If the gradient of a compactly supported `C²` function is bounded by `H` and has
`L¹`-norm at most `L`, then its `L²`-norm is at most `H * L`.  Pointwise
`‖∇χ‖² ≤ H‖∇χ‖`; integrability of `‖∇χ‖` follows from compact support. -/
theorem fderivL2_le_mul {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (h2 : ContDiff ℝ 2 χ)
    (hcs : HasCompactSupport χ) {H L : ℝ}
    (hH : ∀ x, ‖fderiv ℝ χ x‖ ≤ H) (hL : ∫ x, ‖fderiv ℝ χ x‖ ≤ L) :
    ∫ x, ‖fderiv ℝ χ x‖ ^ 2 ≤ H * L := by
  -- `H` is nonnegative whenever the bound `hH` holds at a single point.
  have hHnn : 0 ≤ H := le_trans (norm_nonneg _) (hH 0)
  -- `‖∇χ‖` is continuous with compact support, hence integrable.
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin 3) => ‖fderiv ℝ χ x‖ :=
    (h2.continuous_fderiv (by norm_num)).norm
  have hsupp : HasCompactSupport fun x : EuclideanSpace ℝ (Fin 3) => ‖fderiv ℝ χ x‖ :=
    (hcs.fderiv ℝ).norm
  have hInt : Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ‖fderiv ℝ χ x‖) :=
    hcont.integrable_of_hasCompactSupport hsupp
  have hIntH : Integrable (fun x : EuclideanSpace ℝ (Fin 3) => H * ‖fderiv ℝ χ x‖) :=
    hInt.const_mul H
  -- pointwise bound `‖∇χ‖² ≤ H ‖∇χ‖`
  have hpt : ∀ x : EuclideanSpace ℝ (Fin 3), ‖fderiv ℝ χ x‖ ^ 2 ≤ H * ‖fderiv ℝ χ x‖ := by
    intro x
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (hH x) (norm_nonneg _)
  calc ∫ x, ‖fderiv ℝ χ x‖ ^ 2
      ≤ ∫ x, H * ‖fderiv ℝ χ x‖ :=
        integral_mono_of_nonneg (ae_of_all _ (fun x => sq_nonneg _)) hIntH (ae_of_all _ hpt)
    _ = H * ∫ x, ‖fderiv ℝ χ x‖ := integral_const_mul H _
    _ ≤ H * L := mul_le_mul_of_nonneg_left hL hHnn

end Work.BoseB1Cube
