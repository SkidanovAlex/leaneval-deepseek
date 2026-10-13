import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

/-- The gradient of `x ↦ F (‖x‖ ^ 2)` on `ℝ³` at `z` is `2 * F' (‖z‖ ^ 2) • innerSL ℝ z`
(i.e. the map `v ↦ 2 F'(‖z‖²) ⟪z, v⟫`).  Proved by the chain rule from
`hasStrictFDerivAt_norm_sq`. -/
theorem gradient_comp_normSq (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (z : EuclideanSpace ℝ (Fin 3)) :
    fderiv ℝ (fun x : EuclideanSpace ℝ (Fin 3) => F (‖x‖ ^ 2)) z
      = (2 * deriv F (‖z‖ ^ 2)) • (innerSL ℝ z) := by
  -- `F` is differentiable, so `HasDerivAt F (deriv F (‖z‖²)) (‖z‖²)`.
  have hdF : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hderiv : HasDerivAt F (deriv F (‖z‖ ^ 2)) (‖z‖ ^ 2) :=
    (hdF (‖z‖ ^ 2)).hasDerivAt
  -- the strict derivative of `x ↦ ‖x‖ ^ 2` at `z`.
  have h1 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖ ^ 2)
      (2 • innerSL ℝ z) z := (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  -- the chain rule.
  have h2 : HasFDerivAt (fun x : EuclideanSpace ℝ (Fin 3) => F (‖x‖ ^ 2))
      ((ContinuousLinearMap.toSpanSingleton ℝ (deriv F (‖z‖ ^ 2))) ∘SL (2 • innerSL ℝ z)) z :=
    hderiv.hasFDerivAt.comp z h1
  rw [h2.fderiv]
  -- identify `toSpanSingleton ℝ c ∘SL (2 • innerSL ℝ z)` with `(2 * c) • innerSL ℝ z`.
  ext v
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.toSpanSingleton_apply, innerSL_apply_apply]
  ring

end Work.FTS.PressureOn.Auxiliary
