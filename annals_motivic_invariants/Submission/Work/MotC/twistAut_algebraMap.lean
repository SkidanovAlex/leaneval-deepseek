import Mathlib
import Submission.Work.MotC.Defs
import Submission.Work.MotC.coeffAut_algebraMap

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC

theorem twistAut_algebraMap {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜)
    (τ : WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D) ≃ₐ[D.ext.L]
      WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D)) (l : D.ext.L) :
    Work.MotC.twistAut D τ
        (algebraMap D.ext.L (WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D)) l) =
      algebraMap D.ext.L (WeierstrassCurve.Affine.FunctionField (Work.MotC.baseCurve D))
        (D.sigma l) := by
  -- `twistAut D τ` is the composite of the coefficient action with `τ`, so it acts on the
  -- constant `l` as `coeffAut D` does on `τ (algebraMap l) = algebraMap l`.
  rw [Work.MotC.twistAut, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply]
  -- `τ` is `L`-linear, hence fixes the constants `L`
  rw [τ.commutes l]
  exact coeffAut_algebraMap D l

end Work.MotC
