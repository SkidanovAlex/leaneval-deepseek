import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Calculus

/-- The chain rule for `y ↦ Real.smoothTransition (a * g y)`: since `Real.smoothTransition` is
smooth (indeed `ContDiff ℝ ⊤`) and `y ↦ a * g y` has derivative `a • fderiv ℝ g z`, the derivative
of the composition at `z` is `(deriv Real.smoothTransition (a * g z) * a) • fderiv ℝ g z`. -/
theorem fderiv_smoothTransition_const_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {z : E} (hg : DifferentiableAt ℝ g z) (a : ℝ) :
    fderiv ℝ (fun y => Real.smoothTransition (a * g y)) z
      = (deriv Real.smoothTransition (a * g z) * a) • fderiv ℝ g z := by
  -- `Real.smoothTransition` is differentiable at every point.
  have hd : DifferentiableAt ℝ Real.smoothTransition (a * g z) :=
    (Real.smoothTransition.contDiffAt (n := ⊤)).differentiableAt (by simp)
  -- Its derivative there, as a continuous linear map, is `t ↦ t • deriv smoothTransition (a * g z)`.
  have hout : HasFDerivAt Real.smoothTransition
      (ContinuousLinearMap.toSpanSingleton ℝ (deriv Real.smoothTransition (a * g z))) (a * g z) :=
    hd.hasDerivAt.hasFDerivAt
  -- The inner map `y ↦ a * g y` has derivative `a • fderiv ℝ g z`.
  have hin : HasFDerivAt (fun y => a * g y) (a • fderiv ℝ g z) z := hg.hasFDerivAt.const_mul a
  -- Chain rule.
  have hcomp := hout.comp z hin
  have hfun : (Real.smoothTransition ∘ fun y => a * g y) = fun y => Real.smoothTransition (a * g y) :=
    rfl
  rw [← hfun, hcomp.fderiv]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_apply, smul_eq_mul]
  ring

end Commons.Analysis.Calculus