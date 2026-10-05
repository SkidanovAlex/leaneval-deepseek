import Mathlib
import Submission.Work.RPB.B5.RhoPerDefs

namespace Work.RPB.B5

/-- The middle weight `wM = 1 - wL - wR` is smooth, so its derivative splits as the
difference of the derivatives of the two cutoffs. -/
theorem deriv_wM (δ δA u₂ x : ℝ) :
    deriv (wM δ δA u₂) x = - deriv (wL δ δA) x - deriv (wR δ u₂) x := by
  have dL : DifferentiableAt ℝ (wL δ δA) x :=
    ((wL_contDiff δ δA).differentiable (by norm_num)).differentiableAt
  have dR : DifferentiableAt ℝ (wR δ u₂) x :=
    ((wR_contDiff δ u₂).differentiable (by norm_num)).differentiableAt
  have h1 : HasDerivAt (fun y => 1 - wL δ δA y) (- deriv (wL δ δA) x) x := by
    simpa using dL.hasDerivAt.const_sub 1
  have h2 : HasDerivAt (fun y => 1 - wL δ δA y - wR δ u₂ y)
      (- deriv (wL δ δA) x - deriv (wR δ u₂) x) x :=
    h1.sub dR.hasDerivAt
  have : wM δ δA u₂ = (fun y => 1 - wL δ δA y - wR δ u₂ y) := rfl
  rw [this, h2.deriv]

end Work.RPB.B5
