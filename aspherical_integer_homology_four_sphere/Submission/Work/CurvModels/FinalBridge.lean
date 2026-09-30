/-
# The `curvLe` field of the final assembly from the atlas curvature datum

Area `Submission/Work/CurvModels/`.  Composing the datum `Work.CurvModels.hmodels` with the
delivered bridge `Work.Final.curvLe_of_models` gives the `curvLe` field of
`Work.Final.FinalInputs`:

```
∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe (Work.Final.mhatCov (rt := rt)) K
```

(the parametric Cartan–Hadamard curvature bound of the assembled metric), from

* the atlas curvature datum `Work.CurvModels.ModelCurvature rt.models` (which models each chart
  carries, and that they agree with the geometric metrics on their targets), and
* the smoothness instance `CovariantDerivative.ContMDiffCovariantDerivative` of the Levi-Civita
  connection (the `cov_smooth` field, owned by the LeviCivita area).
-/
import Mathlib
import Submission.Work.CurvModels.Hmodels
import Submission.Work.Final.curvLe_of_models
import Submission.Work.Final.CurvField

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Manifold ContDiff Bundle Topology ENNReal

namespace Work.CurvModels

/-- **The curvature bound of `M̂` from the atlas curvature datum**: the `curvLe` field of
`Work.Final.FinalInputs`, obtained by feeding `Work.CurvModels.hmodels` to
`Work.Final.curvLe_of_models`. -/
theorem curvLe_of_models [rt : Work.Space.RTData] [C : ModelCurvature rt.models]
    [CovariantDerivative.ContMDiffCovariantDerivative (Work.Final.mhatCov (rt := rt))
      Work.Final.smoothGrade] :
    ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe (Work.Final.mhatCov (rt := rt)) K :=
  Work.Final.curvLe_of_models (rt := rt) (hmodels (rt := rt))

/-- **The `curvLe` field of `Work.Final.FinalInputs` from the model curvature datum** — the form in
which the field is registered: the smoothness instance of the Levi-Civita connection is taken from
the `cov_smooth` field of `FinalInputs` itself (`Work.Final.FinalInputs.mhatCov_contMDiff`), so no
instance argument has to be supplied at the call site. -/
theorem curvLe_of_models_finalInputs [D : Work.Final.FinalInputs]
    [C : ModelCurvature D.rt.models] :
    ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe (Work.Final.mhatCov (rt := D.rt)) K :=
  Work.Final.FinalInputs.curvLe_field (hmodels (rt := D.rt))

section Interface

/- The three ways of producing the `curvLe` field of `Work.Final.FinalInputs` from the curvature
datum of this area, checked at build time. -/
variable [D : Work.Final.FinalInputs] [C : ModelCurvature D.rt.models]

/-- Through the `FinalInputs`-level wrapper (no instance argument needed). -/
example : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe (Work.Final.mhatCov (rt := D.rt)) K :=
  curvLe_of_models_finalInputs

/-- Through `Work.Final.FinalInputs.curvLe_field` (the delivered field) and `hmodels`. -/
example : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe (Work.Final.mhatCov (rt := D.rt)) K :=
  Work.Final.FinalInputs.curvLe_field (hmodels (rt := D.rt))

/-- Through the `rt`-level wrapper, with the smoothness instance made available explicitly. -/
example : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe (Work.Final.mhatCov (rt := D.rt)) K := by
  haveI := D.mhatCov_contMDiff
  exact curvLe_of_models (rt := D.rt)

end Interface

end Work.CurvModels
