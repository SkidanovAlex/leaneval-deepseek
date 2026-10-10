import Mathlib
import Submission.Work.PointlessIndexFive.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.PointlessIndexFive

noncomputable section

/-- The base-change homomorphism `E(𝕜) → E(L)` of a quintic twist is injective: it is the
`Point.map` induced by the (injective) structure map `𝕜 → L`.  Consequently it reflects the
origin, which is what transfers `P ≠ 0` from `E(𝕜)` to `E(L)`. -/
theorem baseChange_PL_injective {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) :
    Function.Injective
      (WeierstrassCurve.Affine.Point.baseChange (W' := D.E) 𝕜 D.ext.L) :=
  WeierstrassCurve.Affine.Point.map_injective (Algebra.ofId 𝕜 D.ext.L)

/-- The marked point `P` of order `5` is not the origin; base change to `E(L)` preserves this. -/
theorem PL_ne_zero {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] (D : QuinticTwist 𝕜) : D.PL ≠ 0 := by
  intro h
  refine D.P_ne_zero ?_
  have hkey : D.PL =
      (WeierstrassCurve.Affine.Point.baseChange (W' := D.E) 𝕜 D.ext.L) D.P := rfl
  have h1 : (WeierstrassCurve.Affine.Point.baseChange (W' := D.E) 𝕜 D.ext.L) D.P = 0 := by
    rw [← hkey]; exact h
  exact baseChange_PL_injective D (by rw [h1]; rfl)

end

end Work.PointlessIndexFive
