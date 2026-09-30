/-
# The model curvature datum of a chart

Area `Submission/Work/CurvModels/`.  This file fixes the *data* which a provider of a
`Work.Space.ModelAtlas` must supply about each chart model, so that the atlas knows the sign of
the sectional curvature of its models.

The blueprint's manifold `M̂` carries three metric models:

| model | metric field | region | reference |
|---|---|---|---|
| upper half space (hyperbolic piece, cusp charts) | `uhsMetric` | `{q | 0 < q 3}` | `Curvature.secNonposAt_uhs` |
| filling (polar and cusp-box charts) | `warpedMetric P.f P.h` | `{q | 0 < q 0}` | `Curvature.secNonposAt_fillProfile` |
| flat core | `flatMetric h₀` | all of `E4` | `Curvature.secNonposAt_flat` |

A `ModelData` packages one such model: the metric field, the region on which it *is* the model of
the chart, the proof that its sectional curvature is non-positive there, and the proof that it is a
metric there (first-slot linear and positive definite, the hypotheses of `koszulChr_eq_of_forall`).
The three canonical models are `ModelData.uhs`, `ModelData.warped`, `ModelData.flat`, and there are
"on a subregion" variants (`ModelData.uhsOf`, `ModelData.warpedOf`, `ModelData.corePolar`) for the
case where a provider uses a slightly smaller region than the maximal one.

`Work.CurvModels.ModelCurvature` (in `ModelCurvature.lean`) then attaches one `ModelData` to each
chart of an atlas.
-/
import Mathlib
import Submission.Work.CurvModels.Basic

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

/-- **A model curvature datum**: a metric field, the region in which it is the geometric model of a
chart, and the two facts the atlas contract needs about it — non-positive sectional curvature, and
being a metric (first-slot linear, positive definite) on that region. -/
structure ModelData where
  /-- The metric field of the model, in the standard coordinates of `E4`. -/
  metric : MetricField
  /-- The region of `E4` on which the model is used (it contains the target of every chart
  carrying this model). -/
  region : Set E4
  /-- The model has non-positive sectional curvature on its region. -/
  sec : ∀ q ∈ region, SecNonposAt metric q
  /-- The model is a metric (first-slot linear and positive definite) on its region. -/
  metricAt : ∀ q ∈ region, IsMetricAt metric q

namespace ModelData

/-! ## The three models of the blueprint -/

/-- **The upper half space model** `uhsMetric q = (q 3)⁻² δ` on the upper half space
`{q | 0 < q 3}`: constant sectional curvature `−1`. -/
def uhs : ModelData where
  metric := uhsMetric
  region := {q | 0 < q 3}
  sec := fun q hq => secNonposAt_uhs q hq
  metricAt := fun q hq => isMetricAt_uhsMetric q (ne_of_gt hq)

/-- The upper half space model, on a subregion of the upper half space. -/
def uhsOf (region : Set E4) (h : region ⊆ {q | 0 < q 3}) : ModelData where
  metric := uhsMetric
  region := region
  sec := fun q hq => secNonposAt_uhs q (h hq)
  metricAt := fun q hq => isMetricAt_uhsMetric q (ne_of_gt (h hq))

/-- **The warped filling model** of a `Work.Profiles.FillProfile`, on `{q | 0 < q 0}` (the region
in which the warping functions are positive, nondecreasing and convex — the hypotheses of
`Curvature.secNonposAt_fillProfile`). -/
def warped (P : Work.Profiles.FillProfile) : ModelData where
  metric := warpedMetric P.f P.h
  region := {q | 0 < q 0}
  sec := fun q hq => secNonposAt_fillProfile P q hq
  metricAt := fun q hq =>
    isMetricAt_warpedMetric P.f P.h q (ne_of_gt (P.f_pos (q 0) hq)) (ne_of_gt (P.h_pos (q 0)))

/-- **A general warped model** on an arbitrary region, with the two facts supplied by the caller
(e.g. the warping functions `f = id`, `h = h₀` of the flat core in polar coordinates). -/
def warpedOf (f h : ℝ → ℝ) (region : Set E4)
    (sec : ∀ q ∈ region, SecNonposAt (warpedMetric f h) q)
    (metricAt : ∀ q ∈ region, IsMetricAt (warpedMetric f h) q) : ModelData where
  metric := warpedMetric f h
  region := region
  sec := sec
  metricAt := metricAt

/-- **The flat core** `flatMetric h₀ = diag(1,1,h₀²,h₀²)` on all of `E4`. -/
def flat (h₀ : ℝ) (h0 : h₀ ≠ 0) : ModelData where
  metric := flatMetric h₀
  region := Set.univ
  sec := fun q _ => secNonposAt_flat h₀ h0 q
  metricAt := fun q _ => isMetricAt_flatMetric h₀ h0 q

/-- **The flat core in polar coordinates**: the warped metric with `f = id` and `h = h₀` is the
Euclidean metric `dr² + r²dθ² + h₀²|dw|²` on the half plane `{q | 0 < q 0}`, hence flat. -/
def corePolar (h₀ : ℝ) (h0 : 0 < h₀) : ModelData :=
  warpedOf (fun r : ℝ => r) (fun _ => h₀) {q | 0 < q 0}
    (fun q hq => secNonposAt_warped (fun r : ℝ => r) (fun _ => h₀) q
      contDiff_id (contDiff_const (c := h₀)) hq h0
      (by simp) (by simp) (by simp) (by simp))
    (fun q hq => isMetricAt_warpedMetric _ _ q (ne_of_gt hq) (ne_of_gt h0))

/-! ## Simple constructors -/

/-- A model on a region contained in the region of another one (with the same metric). -/
def restrict (M : ModelData) (region : Set E4) (h : region ⊆ M.region) : ModelData where
  metric := M.metric
  region := region
  sec := fun q hq => M.sec q (h hq)
  metricAt := fun q hq => M.metricAt q (h hq)

@[simp] theorem restrict_metric (M : ModelData) (region : Set E4) (h : region ⊆ M.region) :
    (M.restrict region h).metric = M.metric := rfl

@[simp] theorem uhs_region : uhs.region = {q : E4 | 0 < q 3} := rfl
@[simp] theorem warped_region (P : Work.Profiles.FillProfile) :
    (warped P).region = {q : E4 | 0 < q 0} := rfl
@[simp] theorem flat_region (h₀ : ℝ) (h0 : h₀ ≠ 0) : (flat h₀ h0).region = Set.univ := rfl

end ModelData

end Work.CurvModels
