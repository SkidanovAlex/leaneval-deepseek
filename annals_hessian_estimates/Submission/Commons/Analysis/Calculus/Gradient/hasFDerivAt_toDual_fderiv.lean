import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Calculus.Gradient

open scoped RealInnerProductSpace in
theorem hasFDerivAt_toDual_fderiv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {φ : E → ℝ} {x : E} (h : ContDiffAt ℝ 2 φ x) :
    HasFDerivAt (fun y => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ φ y))
      (InnerProductSpace.continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ φ) x)) x := by
  -- `fderiv ℝ φ` is `C^1` at `x`, hence differentiable there with derivative the second derivative.
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ φ) x := h.fderiv_right (m := 1) (by norm_num)
  have hg : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) x) x :=
    (h1.differentiableAt (by norm_num)).hasFDerivAt
  -- The duality equivalence `toDual` is a linear isometry equivalence, so it is its own derivative.
  have hL := (InnerProductSpace.toDual ℝ E).symm.hasFDerivAt (x := (fderiv ℝ φ) x)
  -- Chain rule.
  have hcomp := hL.comp x hg
  simpa [InnerProductSpace.continuousLinearMapOfBilin, Function.comp_def] using hcomp

end Commons.Analysis.Calculus.Gradient