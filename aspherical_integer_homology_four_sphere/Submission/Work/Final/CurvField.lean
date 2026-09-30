/-
# `Final/`: the curvature field of `FinalInputs`, discharged

The field `curvLe` of `Work.Final.FinalInputs` is `Work.Final.curvLe_of_models` applied to the
model curvature datum (a chart model agreeing with the chart metric near each point and having
non-positive sectional curvature there); that lemma composes the pointwise curvature bridge
`Work.Final.secNonpos_of_chartModels` with `Work.CartanHadamard.curvLe_all`.
-/
import Submission.Work.Final.Discharge
import Submission.Work.Final.curvLe_of_models

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology ENNReal

namespace Work.Final

noncomputable section

namespace FinalInputs

variable [D : FinalInputs]

/-- **The field `curvLe` of `FinalInputs`, discharged**: the curvature bridge
`Work.Final.curvLe_of_models` applied to the model datum `hmodels` (see `NOTES_FINAL.md` §5). -/
theorem curvLe_field
    (hmodels : ∀ x : D.rt.Mhat, ∃ G ∈ D.rt.models.models,
      Work.Curvature.SecNonposAt G ((extChartAt Work.Space.I4 x) x) ∧
      Filter.Eventually (fun q => ∀ a b : Work.Space.E4,
          Submission.ChartConnection.chartGram (I := Work.Space.I4) x
            ((extChartAt Work.Space.I4 x).symm q) a b = G q a b)
        (nhds ((extChartAt Work.Space.I4 x) x))) :
    ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe (mhatCov (rt := D.rt)) K := by
  haveI := D.mhatCov_contMDiff
  exact Work.Final.curvLe_of_models (rt := D.rt) hmodels

end FinalInputs

end

end Work.Final
