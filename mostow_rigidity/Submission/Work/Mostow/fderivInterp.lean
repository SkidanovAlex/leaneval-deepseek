import Mathlib

namespace Work.Mostow

/-- Derivative of the linear interpolation between the identity and a `C¹` map. -/
theorem fderivInterp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → E) (hf : ContDiff ℝ 1 f) (t : ℝ) (x : E) :
    fderiv ℝ (fun y => (1 - t) • y + t • f y) x
      = (1 - t) • (1 : E →L[ℝ] E) + t • fderiv ℝ f x := by
  have hfd : DifferentiableAt ℝ f x := hf.differentiable_one.differentiableAt
  have h1 : HasFDerivAt (fun y : E => (1 - t) • y) ((1 - t) • (1 : E →L[ℝ] E)) x :=
    (hasFDerivAt_id x).const_smul (1 - t)
  have h2 : HasFDerivAt (fun y : E => t • f y) (t • fderiv ℝ f x) x :=
    hfd.hasFDerivAt.const_smul t
  have h3 : HasFDerivAt (fun y : E => (1 - t) • y + t • f y)
      ((1 - t) • (1 : E →L[ℝ] E) + t • fderiv ℝ f x) x := h1.add h2
  exact h3.fderiv

end Work.Mostow
