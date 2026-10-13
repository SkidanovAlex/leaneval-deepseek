import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.BSIdentP.Levels

/-- For a two-variable function `F` differentiable at `(w, η)`, the derivative of the slice
`θ ↦ F w θ` at `η` is the Fréchet derivative at `(w, η)` applied to the direction `(0, 1)`. -/
theorem deriv_slice_eq_fderiv {F : ℝ → ℝ → ℝ} {w η : ℝ}
    (hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => F p.1 p.2) (w, η)) :
    deriv (fun θ : ℝ => F w θ) η = fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2) (w, η) (0, 1) := by
  -- The slice `θ ↦ F w θ` is the composite of `p ↦ F p.1 p.2` with the affine map
  -- `θ ↦ (w, θ)`, whose Fréchet derivative is `ContinuousLinearMap.inr ℝ ℝ ℝ`
  -- (the second-coordinate injection `1 ↦ (0, 1)`).
  have h1 : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      (fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2) (w, η)) (w, η) := hd.hasFDerivAt
  have h2 : HasFDerivAt (fun θ : ℝ => (w, θ)) (ContinuousLinearMap.inr ℝ ℝ ℝ) η :=
    hasFDerivAt_prodMk_right w η
  have h3 : HasFDerivAt (fun θ : ℝ => F w θ)
      ((fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2) (w, η)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) η :=
    h1.comp η h2
  rw [(h3.hasDerivAt).deriv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

end Work.FTS.BSIdentP.Levels
