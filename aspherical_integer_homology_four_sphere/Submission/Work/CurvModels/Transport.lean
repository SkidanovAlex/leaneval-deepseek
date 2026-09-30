/-
# Transporting the curvature sign of the three models to an arbitrary chart model

Area `Submission/Work/CurvModels/`.  A provider of the atlas of `M̂` does not use the metric fields
`Work.Curvature.uhsMetric` / `warpedMetric` / `flatMetric` themselves as chart models: the field
`Work.Space.ModelAtlas.model_pos` requires the model to be positive definite on *all* of `E4`, so
the model of a chart is a smooth total modification of the geometric metric which agrees with it on
the chart target (for instance `q ↦ (ψ (q 3))⁻² • δ` for the upper half space model, with `ψ`
smooth and positive with `ψ t = t` for `t ≥ δ`).

This file gives the transport in the form such a provider needs, for each of the three models: if a
metric field `G` agrees, near a point `q` of the region of the model, with the geometric metric of
the model, then `SecNonposAt G q`.  The ingredients are the locality theorem
`Work.CurvModels.SecNonposAt_congr` and the model producers of the curvature chapter
(`Work.Curvature.secNonposAt_uhs`, `secNonposAt_fillProfile`, `secNonposAt_flat`).

Typical use (a `Work.RTInstance.ChartLayer`-style `uhs` chart with margin `δ`, whose target lies in
`{q | δ < q 3}`):

```lean
theorem ChartLayer.secNonposAt_uhs {δ : ℝ} (hδ : 0 < δ) {q : E4} (hq : δ < q 3) :
    Curvature.SecNonposAt (Curvature.MetricField) (uhsModel δ) q :=
  Work.CurvModels.secNonposAt_of_agreesNear_uhsMetric (lt_trans hδ hq)
    (AgreesNear.of_mem_open isOpen_lt_const (lt_trans hδ hq)
      (fun q' hq' a b => uhsModel_eq_uhsMetric hδ (le_of_lt hq') a b))
```
-/
import Mathlib
import Submission.Work.CurvModels.Basic
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

/-! ## The model metrics are metrics near the points of their regions -/

/-- `uhsMetric` is a metric near every point of the upper half space. -/
theorem isMetricNear_uhsMetric {q : E4} (hq : 0 < q 3) : IsMetricNear uhsMetric q := by
  have hmem : {q' : E4 | 0 < q' 3} ∈ 𝓝 q :=
    ((coord 3).continuous.continuousAt).preimage_mem_nhds (isOpen_Ioi.mem_nhds hq)
  exact Filter.eventually_of_mem hmem fun q' hq' => isMetricAt_uhsMetric q' (ne_of_gt hq')

/-- The filling model of a profile is a metric near every point of `{q | 0 < q 0}`. -/
theorem isMetricNear_warpedMetric (P : Work.Profiles.FillProfile) {q : E4} (hq : 0 < q 0) :
    IsMetricNear (warpedMetric P.f P.h) q := by
  have hmem : {q' : E4 | 0 < q' 0} ∈ 𝓝 q :=
    ((coord 0).continuous.continuousAt).preimage_mem_nhds (isOpen_Ioi.mem_nhds hq)
  exact Filter.eventually_of_mem hmem fun q' hq' =>
    isMetricAt_warpedMetric P.f P.h q' (ne_of_gt (P.f_pos (q' 0) hq')) (ne_of_gt (P.h_pos (q' 0)))

/-- The flat model is a metric everywhere. -/
theorem isMetricNear_flatMetric (h₀ : ℝ) (h0 : h₀ ≠ 0) (q : E4) :
    IsMetricNear (flatMetric h₀) q :=
  Filter.Eventually.of_forall fun q' => isMetricAt_flatMetric h₀ h0 q'

/-! ## The three transports -/

/-- **The upper half space case**: a field agreeing with `uhsMetric` near a point of the upper half
space has non-positive sectional curvature there. -/
theorem secNonposAt_of_agreesNear_uhsMetric {G : MetricField} {q : E4} (hq : 0 < q 3)
    (h : AgreesNear uhsMetric G q) : SecNonposAt G q :=
  SecNonposAt_congr (isMetricNear_uhsMetric hq) h (secNonposAt_uhs q hq)

/-- **The warped filling case**: a field agreeing with the filling model of a profile near a point
`q` with `0 < q 0` has non-positive sectional curvature there. -/
theorem secNonposAt_of_agreesNear_warpedMetric {G : MetricField} (P : Work.Profiles.FillProfile)
    {q : E4} (hq : 0 < q 0) (h : AgreesNear (warpedMetric P.f P.h) G q) : SecNonposAt G q :=
  SecNonposAt_congr (isMetricNear_warpedMetric P hq) h (secNonposAt_fillProfile P q hq)

/-- **The flat core case**: a field agreeing with `flatMetric h₀` near any point has non-positive
sectional curvature there (it is flat). -/
theorem secNonposAt_of_agreesNear_flatMetric {G : MetricField} (h₀ : ℝ) (h0 : h₀ ≠ 0) {q : E4}
    (h : AgreesNear (flatMetric h₀) G q) : SecNonposAt G q :=
  SecNonposAt_congr (isMetricNear_flatMetric h₀ h0 q) h (secNonposAt_flat h₀ h0 q)

/-! ## The same transports in the "open set" form -/

/-- **The upper half space case, on an open set.**  If `V` is open, contained in the upper half
space, and `G` agrees with `uhsMetric` on `V`, then `SecNonposAt G q` for every `q ∈ V`. -/
theorem secNonposAt_of_forall_eq_uhsMetric {G : MetricField} {V : Set E4} (hVo : IsOpen V)
    (hsub : V ⊆ {q : E4 | 0 < q 3}) (h : ∀ q ∈ V, ∀ a b : E4, G q a b = uhsMetric q a b)
    {q : E4} (hq : q ∈ V) : SecNonposAt G q :=
  secNonposAt_of_agreesNear_uhsMetric (hsub hq)
    (AgreesNear.of_mem_open hVo hq fun q' hq' a b => (h q' hq' a b).symm)

/-- **The warped filling case, on an open set.** -/
theorem secNonposAt_of_forall_eq_warpedMetric {G : MetricField} (P : Work.Profiles.FillProfile)
    {V : Set E4} (hVo : IsOpen V) (hsub : V ⊆ {q : E4 | 0 < q 0})
    (h : ∀ q ∈ V, ∀ a b : E4, G q a b = warpedMetric P.f P.h q a b) {q : E4} (hq : q ∈ V) :
    SecNonposAt G q :=
  secNonposAt_of_agreesNear_warpedMetric P (hsub hq)
    (AgreesNear.of_mem_open hVo hq fun q' hq' a b => (h q' hq' a b).symm)

/-- **The flat core case, on an open set.** -/
theorem secNonposAt_of_forall_eq_flatMetric {G : MetricField} (h₀ : ℝ) (h0 : h₀ ≠ 0)
    {V : Set E4} (hVo : IsOpen V)
    (h : ∀ q ∈ V, ∀ a b : E4, G q a b = flatMetric h₀ q a b) {q : E4} (hq : q ∈ V) :
    SecNonposAt G q :=
  secNonposAt_of_agreesNear_flatMetric h₀ h0
    (AgreesNear.of_mem_open hVo hq fun q' hq' a b => (h q' hq' a b).symm)

end Work.CurvModels
