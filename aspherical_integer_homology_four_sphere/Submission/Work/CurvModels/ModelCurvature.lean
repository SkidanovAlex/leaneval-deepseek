/-
# The curvature datum of a model atlas, and the per-point case split

Area `Submission/Work/CurvModels/`.  A `Work.Space.ModelAtlas M` carries, for each chart `i`, a
metric model `A.model i` — an abstract positive definite smooth family on `E4`, with no hypothesis
on its curvature.  This file fixes what a *provider* of such an atlas must say about its models for
the curvature of `M̂` to be computable, namely `Work.CurvModels.ModelCurvature`:

* `kind i : ModelData` — which of the documented metric models (`ModelData.uhs`,
  `ModelData.warped P`, `ModelData.flat h₀`, or a variant) the `i`-th chart carries;
* `eq_model` — on the target of the `i`-th chart, the atlas model *is* that metric field;
* `target_subset` — the target of the `i`-th chart lies in the region of that model.

Given such a datum, **the per-point case split** `secNonposAt_field_of_mem` says: for every chart
`i` and every `x` in its source, the atlas model of that chart has non-positive sectional curvature
at the image of `x`.  The proof is the case split, point by point:

* the image `(A.chart i) x` lies in the open target of the chart, hence (by `target_subset`) in the
  region of the model, where the model has non-positive curvature and is a genuine metric
  (`ModelData.sec`, `ModelData.metricAt`);
* on the whole (open) target the atlas model agrees with the model (`eq_model`), and agreement on
  an open neighbourhood is exactly the hypothesis of the locality theorem
  `Work.CurvModels.SecNonposAt_congr` — which transports the sign of the curvature from the
  geometric model to the atlas model.

`Work.CurvModels.hmodels` (`Hmodels.lean`) is the datum required by the final assembly
(`Work.Final.FinalInputs`), and `Work.CurvModels.curvLe_of_models` (`FinalBridge.lean`) is the
`curvLe` field itself.
-/
import Mathlib
import Submission.Work.CurvModels.ModelData
import Submission.Work.CurvModels.SecNonposAt_congr

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Filter Topology
open scoped Manifold ContDiff Bundle Topology
open Work.Curvature

namespace Work.CurvModels

/-- **The curvature datum of a model atlas.**  Every chart of the atlas is one of the documented
metric models on its target: `kind i` is the model of the `i`-th chart, `eq_model` says that the
abstract atlas model agrees with it on the target, and `target_subset` that the target lies in the
region of validity of the model. -/
class ModelCurvature {M : Type*} [TopologicalSpace M] (A : Work.Space.ModelAtlas M) where
  /-- The metric model carried by each chart of the atlas. -/
  kind : Fin A.n → ModelData
  /-- On the target of a chart, the atlas model is the model metric. -/
  eq_model : ∀ i : Fin A.n, ∀ q ∈ (A.chart i).target, ∀ a b : Work.Space.E4,
    A.field i q a b = (kind i).metric q a b
  /-- The target of a chart lies in the region of its model. -/
  target_subset : ∀ i : Fin A.n, (A.chart i).target ⊆ (kind i).region

namespace ModelCurvature

variable {M : Type*} [TopologicalSpace M] [A : Work.Space.ModelAtlas M] [C : ModelCurvature A]

/-- **The per-point case split.**  If `x` lies in the source of the `i`-th chart of the atlas, then
the model of that chart has non-positive sectional curvature at the image of `x`.

The case split is on the model `C.kind i`: whichever of the three documented models the chart
carries, the point `(A.chart i) x` lies in its region (via `target_subset`), where the model is a
non-positively curved metric (`ModelData.sec`), and on the open target the atlas model agrees with
it (`eq_model`), so `SecNonposAt_congr` transfers the sign. -/
theorem secNonposAt_field_of_mem {x : M} {i : Fin A.n} (hx : x ∈ (A.chart i).source) :
    SecNonposAt (A.field i) (A.chart i x) := by
  have hxt : (A.chart i) x ∈ (A.chart i).target := (A.chart i).map_source hx
  have hreg : (A.chart i) x ∈ (C.kind i).region := C.target_subset i hxt
  have hVo : IsOpen (A.chart i).target := (A.chart i).open_target
  refine SecNonposAt_congr (G := (C.kind i).metric) (G' := A.field i)
    (IsMetricNear.of_mem_open hVo hxt fun q hq => (C.kind i).metricAt q (C.target_subset i hq))
    (AgreesNear.of_mem_open hVo hxt fun q hq a b => (C.eq_model i q hq a b).symm) ?_
  exact (C.kind i).sec _ hreg

/-- The same statement for the preferred chart of the point: the model of the chart of `x` has
non-positive sectional curvature at the image of `x`. -/
theorem secNonposAt_field_chart (x : M) :
    SecNonposAt (A.field (A.indexOf x)) (A.chart (A.indexOf x) x) :=
  secNonposAt_field_of_mem (A := A) (A.indexOf_mem x)

end ModelCurvature

end Work.CurvModels
