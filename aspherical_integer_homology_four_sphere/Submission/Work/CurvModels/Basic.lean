/-
# The model curvature chapter: metric fields, their good behaviour, and locality

Area `Submission/Work/CurvModels/` (namespace `Work.CurvModels`).  This file is the *definition
layer*: it fixes the predicates in terms of which the whole area is phrased.

## Why these predicates

The curvature chapter `Work.Curvature` computes the curvature of a *metric field*
`G : MetricField = E4 → E4 → E4 → ℝ` through the Christoffel symbol `koszulChr`, which is defined
by `Classical.choose` from the *Koszul formula* (`koszulChr G q a b` is a solution of
`G q · c = koszulRHS G q a b c`).  Two consequences shape this chapter:

* the *uniqueness/computation rule* `koszulChr_eq_of_forall` needs two hypotheses on the metric at
  the point: first-slot linearity (`G q (x - y) c = G q x c - G q y c`) and positive definiteness;
* `SecNonposAt G q` is a *local* property of the germ of `G` at `q` (everything in
  `modelCurv G q` is a derivative at `q`, except the single evaluation `G q (…) u`), but this is
  not visible from the definition: it has to be proved, and the proof goes through the
  computation rule above.

Hence the two predicates of this file:

* `IsMetricAt G q` — `G q` is a first-slot-linear positive definite form (the hypotheses of
  `koszulChr_eq_of_forall` at the point `q`);
* `IsMetricNear G q` — `IsMetricAt G ·` holds on a neighbourhood of `q`;

and the relation `AgreesNear G G' q` — `G` and `G'` agree pointwise on a neighbourhood of `q`.

The chapter's main locality theorem, `Work.CurvModels.SecNonposAt_congr`
(`SecNonposAt_congr.lean`), is the payoff: **`SecNonposAt` only depends on the germ** of the metric
field.  It is what allows one to *replace* a chart model by the geometric model metric
(`uhsMetric`/`warpedMetric`/`flatMetric`) when computing the sign of the sectional curvature of
the chart — the situation of the atlas of `M̂`, where the model of a chart is only required
(by `Work.Space.ModelAtlas`) to be *some* positive definite smooth family agreeing with the
geometric metric on the chart target.

## Main definitions

* `Work.CurvModels.IsMetricAt`, `Work.CurvModels.IsMetricNear`, `Work.CurvModels.AgreesNear`;
* the canonical instances `IsMetricAt` of the three blueprint metrics on their regions:
  `isMetricAt_uhsMetric`, `isMetricAt_warpedMetric` (pointwise, profile hypotheses at `q 0`),
  `isMetricAt_flatMetric`.

-/
import Mathlib
import Submission.Work.Curvature.Main
import Submission.Work.Curvature.ProfileSec
import Submission.Work.Space.Main

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

/-! ## The predicates -/

/-- **`G` is a metric at `q`**: the form `G q` is linear in its first slot (in the subtraction
form needed by the Koszul uniqueness rule) and positive definite. -/
def IsMetricAt (G : MetricField) (q : E4) : Prop :=
  (∀ x y c : E4, G q (x - y) c = G q x c - G q y c) ∧ (∀ x : E4, x ≠ 0 → 0 < G q x x)

/-- **`G` is a metric near `q`**: `IsMetricAt G ·` holds on a neighbourhood of `q`. -/
def IsMetricNear (G : MetricField) (q : E4) : Prop := ∀ᶠ q' in 𝓝 q, IsMetricAt G q'

/-- **`G` and `G'` agree near `q`**: they have the same values, in both vector arguments, on a
neighbourhood of `q`. -/
def AgreesNear (G G' : MetricField) (q : E4) : Prop :=
  ∀ᶠ q' in 𝓝 q, ∀ a b : E4, G q' a b = G' q' a b

/-! ## Elementary API -/

namespace IsMetricAt

variable {G : MetricField} {q : E4}

theorem sub_fst (h : IsMetricAt G q) (x y c : E4) : G q (x - y) c = G q x c - G q y c := h.1 x y c

theorem pos (h : IsMetricAt G q) {x : E4} (hx : x ≠ 0) : 0 < G q x x := h.2 x hx

theorem congr_apply (h : IsMetricAt G q) {G' : MetricField} (hq : ∀ x y : E4, G q x y = G' q x y) :
    IsMetricAt G' q :=
  ⟨fun x y c => by rw [← hq (x - y) c, ← hq x c, ← hq y c, h.sub_fst x y c],
   fun x hx => by rw [← hq x x]; exact h.pos hx⟩

end IsMetricAt

namespace AgreesNear

variable {G G' : MetricField} {q : E4}

theorem refl (G : MetricField) (q : E4) : AgreesNear G G q := Filter.Eventually.of_forall fun _ _ _ => rfl

theorem symm (h : AgreesNear G G' q) : AgreesNear G' G q := h.mono fun _ hq a b => (hq a b).symm

/-- Agreement extends the relation to a neighbourhood which is also open. -/
theorem exists_open (h : AgreesNear G G' q) :
    ∃ V : Set E4, IsOpen V ∧ q ∈ V ∧ ∀ q' ∈ V, ∀ a b : E4, G q' a b = G' q' a b := by
  obtain ⟨S, hS, hSsub⟩ := h.exists_mem
  refine ⟨interior S, isOpen_interior, mem_interior_iff_mem_nhds.mpr hS, fun q' hq' a b => ?_⟩
  exact hSsub q' (interior_subset hq') a b

end AgreesNear

/-- **`IsMetricNear` from an open set.**  If `V` is open, contains `q`, and `G` is a metric at
every point of `V`, then `G` is a metric near `q`. -/
theorem IsMetricNear.of_mem_open {G : MetricField} {V : Set E4} (hVo : IsOpen V) {q : E4}
    (hq : q ∈ V) (h : ∀ q' ∈ V, IsMetricAt G q') : IsMetricNear G q :=
  Filter.eventually_of_mem (hVo.mem_nhds hq) h

/-- **`AgreesNear` from an open set.** -/
theorem AgreesNear.of_mem_open {G G' : MetricField} {V : Set E4} (hVo : IsOpen V) {q : E4}
    (hq : q ∈ V) (h : ∀ q' ∈ V, ∀ a b : E4, G q' a b = G' q' a b) : AgreesNear G G' q :=
  Filter.eventually_of_mem (hVo.mem_nhds hq) h

/-- An eventual equality of metric fields gives `AgreesNear`. -/
theorem AgreesNear.of_eventuallyEq {G G' : MetricField} {q : E4} (h : G =ᶠ[𝓝 q] G') :
    AgreesNear G G' q :=
  h.mono fun _ hq a b => congrFun (congrFun hq a) b

/-- Conversely. -/
theorem AgreesNear.eventuallyEq {G G' : MetricField} {q : E4} (h : AgreesNear G G' q) :
    G =ᶠ[𝓝 q] G' :=
  h.mono fun _ hq => funext fun a => funext fun b => hq a b

/-! ## The three blueprint metrics are metrics in the sense of this chapter -/

/-- The upper half space metric is a metric at any point of the upper half space. -/
theorem isMetricAt_uhsMetric (q : E4) (hq : q 3 ≠ 0) : IsMetricAt uhsMetric q :=
  ⟨fun x y c => uhsMetric_sub_fst q x y c, fun x hx => uhsMetric_pos q hq x hx⟩

/-- The warped metric is a metric wherever the warping functions do not vanish. -/
theorem isMetricAt_warpedMetric (f h : ℝ → ℝ) (q : E4) (hf : f (q 0) ≠ 0) (hh : h (q 0) ≠ 0) :
    IsMetricAt (warpedMetric f h) q :=
  ⟨fun x y c => warpedMetric_sub_fst f h q x y c, fun x hx => warpedMetric_pos' f h q hf hh x hx⟩

/-- The flat metric is a metric everywhere (for `h₀ ≠ 0`). -/
theorem isMetricAt_flatMetric (h₀ : ℝ) (h0 : h₀ ≠ 0) (q : E4) : IsMetricAt (flatMetric h₀) q :=
  ⟨fun x y c => flatMetric_sub_fst h₀ q x y c, fun x hx => flatMetric_pos h₀ h0 q x hx⟩

end Work.CurvModels
