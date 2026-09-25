import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmDefs
import Submission.Work.CR.Flat.Cauchy.bmPotential_solves_dbar
import Submission.Work.CR.Flat.Cauchy.bmPotential_contDiff_one
import Submission.Work.CR.Flat.Polydisc

open scoped NNReal ENNReal
open scoped Convolution
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-- **The Bochner–Martinelli potential commutes with directional derivatives.**

For a family `G` of `C¹` functions supported in the open half-size polydisc (so that
`bmPotential G` is `C¹` by `bmPotential_contDiff_one`), the derivative of the potential is the
potential of the derivative:

`∂_v (bmPotential G)(z) = bmPotential (fun j y => (∂_v G_j)(y)) (z)`.

This is the translation invariance of the kernel combined with dominated convergence: the
difference quotient `[(bmPotential G)(z + t v) - (bmPotential G)(z)] / t` equals
`bmPotential (fun j y => [G_j (y + t v) - G_j y]/t)(z)` by the change of variables `ζ ↦ ζ + t v`
in the absolutely convergent integral, and `t → 0` gives the claim. -/
theorem fderiv_bmPotential {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {R : Fin n → ℝ}
    (hR : ∀ j, 0 < R j) {G : Fin n → (Fin n → ℂ) → ℂ} (hG : ∀ j, ContDiff ℝ 1 (G j))
    (hsup : ∀ j z, (∃ k, R k / 2 ≤ ‖z k - c k‖) → G j z = 0) (z v : Fin n → ℂ) :
    fderiv ℝ (fun z => bmPotential G z) z v
      = bmPotential (fun j y => fderiv ℝ (G j) y v) z := by
  have hcs : ∀ j, HasCompactSupport (G j) := fun j =>
    hasCompactSupport_of_halfPolydisc hR (fun y hy => hsup j y hy)
  have hloc : ∀ j, LocallyIntegrable (bmKernel j : (Fin n → ℂ) → ℂ) :=
    fun j => locallyIntegrable_bmKernel hn j
  -- The derivative of each term of the convolution sum, by differentiation under the integral.
  have hderiv : ∀ j, HasFDerivAt (fun w => (bmKernel j ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G j) w)
      ((bmKernel j ⋆[ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ), volume]
        fderiv ℝ (G j)) z) z :=
    fun j => (hcs j).hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ) (hloc j) (hG j) z
  have hF0 : HasFDerivAt (∑ j, fun w => (bmKernel j ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G j) w)
      (∑ j, (bmKernel j ⋆[ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ), volume]
        fderiv ℝ (G j)) z) z :=
    HasFDerivAt.sum (fun j _ => hderiv j)
  have hFeq : (∑ j, fun w => (bmKernel j ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G j) w)
      = fun w => ∑ j, (bmKernel j ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G j) w := by
    funext w
    simp [Finset.sum_apply]
  have hF : HasFDerivAt (fun w => ∑ j, (bmKernel j ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G j) w)
      (∑ j, (bmKernel j ⋆[ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ), volume]
        fderiv ℝ (G j)) z) z :=
    hFeq ▸ hF0
  -- Evaluate the derivative of the `j`-th term along `v` as an integral against the kernel.
  have key : ∀ j, ((bmKernel j ⋆[ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ),
        volume] fderiv ℝ (G j)) z) v
      = - ∫ ζ, bmKernel j (ζ - z) * (fderiv ℝ (G j) ζ) v := by
    intro j
    rw [MeasureTheory.convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ) (hloc j)
      ((hcs j).fderiv ℝ) ((hG j).continuous_fderiv one_ne_zero)]
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
    rw [integral_bmKernel_sub_eq j (fun y => fderiv ℝ (G j) y v) z]
    simp
  have hbm : (fun z => bmPotential G z)
      = fun y => -∑ j, (bmKernel j ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] G j) y := by
    funext w
    rw [bmPotential_eq_neg_conv]
  have hd : HasFDerivAt (fun z => bmPotential G z)
      (-(∑ j, (bmKernel j ⋆[ContinuousLinearMap.precompR (Fin n → ℂ) (ContinuousLinearMap.mul ℝ ℂ),
        volume] fderiv ℝ (G j)) z)) z := by
    rw [hbm]
    exact hF.neg
  rw [hd.fderiv]
  simp only [neg_apply, sum_apply]
  have hsum : (∑ j, ((bmKernel j ⋆[ContinuousLinearMap.precompR (Fin n → ℂ)
        (ContinuousLinearMap.mul ℝ ℂ), volume] fderiv ℝ (G j)) z) v)
      = ∑ j, - ∫ ζ, bmKernel j (ζ - z) * (fderiv ℝ (G j) ζ) v :=
    Finset.sum_congr rfl (fun j _ => key j)
  rw [hsum, Finset.sum_neg_distrib, neg_neg]
  simp only [bmPotential]

end Work.CR.Flat.Cauchy
