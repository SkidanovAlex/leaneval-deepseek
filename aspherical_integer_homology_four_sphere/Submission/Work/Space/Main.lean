/-
# The assembled space `M̂`: the interface of the area `Space/`

This is the top file of the area: a single datum `RTData` from which *all* the structures of `M̂`
follow as instances, and the list of statements that the rest of the project consumes.

## What a caller provides

`RTData` consists of

* `toAssembly : Work.Space.Assembly` — the topological assembly: the hyperbolic piece `M̄` (a compact
  connected Hausdorff space), the five filling pieces `[-1,1]² × T_v`, and the gluing
  homeomorphism between the cusped boundary of `M̄` and the boundary of the filling pieces;
* `models : Work.Space.ModelAtlas `Mhat — the finite atlas of `M̂` together with the metric
  model of each chart (the upper half space metric, the warped filling metric, the flat core
  metric) and their smoothness/symmetry/positive-definiteness;
* `isometry : models.Isometry` — the transitions between the charts are isometries of the models;
* `transition_smooth` — every transition between two charts of the finite atlas is `C^∞`.

## What a caller gets (as global instances)

```
instance : TopologicalSpace Mhat                -- from Assembly
instance : T2Space core.Mhat
instance : CompactSpace core.Mhat
instance : ConnectedSpace core.Mhat
instance : ChartedSpace E4 core.Mhat           -- Work.Space.RTData.instChartedSpace
instance : IsManifold I4 ∞ core.Mhat           -- Work.Space.RTData.instIsManifold
instance : SecondCountableTopology core.Mhat   -- Work.Space.RTData.instSecondCountable
instance : RiemannianBundle (fun y ↦ TangentSpace I4 y)
instance : IsContMDiffRiemannianBundle I4 ∞ E4 (fun y ↦ TangentSpace I4 y)
```

and the global instance `[D : RTData] : D.models.HasIsometry`, so the metric theorems below apply.

## The statements the rest of the project consumes

* `Work.Space.RTData.chartGram_is_model` — `∀ x, ∃ G ∈ D.models.models`, `∀ᶠ q in
  𝓝 (extChartAt I4 x x)`, `chartGram x ((extChartAt I4 x).symm q) a b = G q a b`: the hypothesis
  of `Work.Curvature.curvLe_of_models` (CURV Part 2).
* `Work.Space.RTData.Aset_sup_Bset` — the two open sets of the Mayer–Vietoris cover.
* the homotopy equivalences `Aset ≃ₕ M̄`, `Bset ≃ₕ ⊔ T_v`, `Aset ⊓ Bset ≃ₕ ⊔ ∂[-1,1]² × T_v`.

## How to use it

```
instance : RTData := ⟨myAssembly, myModelAtlas, myIsometry, myTransitionSmoothness⟩
-- from here on everything above is available by typeclass inference
```
-/
import Mathlib
import Submission.Work.Space.MetricChart
import Submission.Work.Space.Split

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open TopologicalSpace
open scoped Manifold ContDiff Topology Bundle
open Bundle

namespace Work.Space

/-- **The data assembling `M̂`**: the topological assembly, the finite atlas with its isometric
metric models, and the smoothness of the transitions.  It is a *class* with instance fields, so a
single `instance : RTData` makes every structure of `M̂` available by typeclass inference. -/
class RTData where
  /-- The topological assembly (hyperbolic piece, filling pieces, gluing). -/
  [core : Assembly]
  /-- The finite atlas with its metric models. -/
  [models : ModelAtlas core.Mhat]
  /-- `M̂` is a smooth manifold in the model `I4`. -/
  [manifold : IsManifold I4 (((⊤ : ℕ∞) : WithTop ℕ∞)) core.Mhat]
  /-- The transitions are isometries of the models. -/
  isometry : models.Isometry
  /-- Every transition of the finite atlas is smooth. -/
  transition_smooth : ∀ i j : Fin models.n,
    ContDiffOn ℝ ∞ ((models.chart j : core.Mhat → E4) ∘ (models.chart i).symm)
      ((models.chart i).symm ≫ₕ models.chart j).source

namespace RTData

/-- The space `M̂` of the assembled datum. -/
abbrev Mhat (D : RTData) : Type _ := D.core.Mhat

/-! ### The instances -/

instance instFinAtlas [D : RTData] : FinAtlas D.Mhat := D.models.toFinAtlas

instance instChartedSpace [D : RTData] : ChartedSpace E4 D.Mhat := D.models.toChartedSpace

instance instIsManifold [D : RTData] : IsManifold I4 ∞ D.Mhat :=
  isManifold_of_contDiffOn_transitions_infty D.models.toFinAtlas D.transition_smooth

instance instSecondCountable [D : RTData] : SecondCountableTopology D.Mhat :=
  secondCountable_of_finAtlas (A := D.instFinAtlas)

instance instHasIsometry [D : RTData] : D.models.HasIsometry := ⟨D.isometry⟩

instance instRiemannianBundle [D : RTData] :
    RiemannianBundle (fun y : D.Mhat => TangentSpace I4 y) :=
  ModelAtlas.instRiemannianBundle (A := D.models)

instance instIsContMDiffRiemannianBundle [D : RTData] :
    IsContMDiffRiemannianBundle I4 (((⊤ : ℕ∞) : WithTop ℕ∞)) E4
      (fun y : D.Mhat => TangentSpace I4 y) :=
  ModelAtlas.instIsContMDiffRiemannianBundle (A := D.models)

/-- **The Riemannian metric of `M̂`**, as a `C^∞` Riemannian metric on the tangent bundle (the
`gM` of the blueprint's `Space/` contract). -/
noncomputable def gM [D : RTData] :
    Bundle.ContMDiffRiemannianMetric I4 (((⊤ : ℕ∞) : WithTop ℕ∞)) E4
      (fun y : D.Mhat => TangentSpace I4 y) :=
  ModelAtlas.contMDiffMetric (A := D.models)

/-! ### The statements consumed by the rest of the project -/

/-- **`chartGram` is a model** — the hypothesis of `Work.Curvature.curvLe_of_models`. -/
theorem chartGram_is_model [D : RTData] (x : D.Mhat) :
    ∃ G ∈ D.models.models, ∀ᶠ q in 𝓝 ((extChartAt I4 x) x), ∀ a b : E4,
      Submission.ChartConnection.chartGram (I := I4) x ((extChartAt I4 x).symm q) a b = G q a b :=
  ModelAtlas.chartGram_is_model (A := D.models) x

/-- **The Mayer–Vietoris cover** `A ∪ B = M̂`. -/
theorem Aset_sup_Bset [D : RTData] :
    (D.core.Aset : Opens D.Mhat) ⊔ D.core.Bset = ⊤ :=
  Assembly.Aset_sup_Bset D.core

end RTData

/-! ### Sanity check: the instances all fire from a single `[D : RTData]` -/

section Interface

variable [D : Work.Space.RTData]

example : TopologicalSpace D.Mhat := inferInstance
example : T2Space D.Mhat := inferInstance
example : CompactSpace D.Mhat := inferInstance
example : ConnectedSpace D.Mhat := inferInstance
example : ChartedSpace E4 D.Mhat := inferInstance
example : IsManifold I4 ∞ D.Mhat := inferInstance
example : IsManifold I4 1 D.Mhat := inferInstance
example : SecondCountableTopology D.Mhat := inferInstance
example : RiemannianBundle (fun y : D.Mhat => TangentSpace I4 y) := inferInstance
example : IsContMDiffRiemannianBundle I4 ∞ E4 (fun y : D.Mhat => TangentSpace I4 y) :=
  inferInstance
example : D.models.HasIsometry := inferInstance
example (x : D.Mhat) : ∃ G ∈ D.models.models, ∀ᶠ q in 𝓝 ((extChartAt I4 x) x), ∀ a b : E4,
    Submission.ChartConnection.chartGram (I := I4) x ((extChartAt I4 x).symm q) a b = G q a b :=
  Work.Space.RTData.chartGram_is_model x
example : (D.core.Aset : TopologicalSpace.Opens D.Mhat) ⊔ D.core.Bset = ⊤ :=
  Work.Space.RTData.Aset_sup_Bset

end Interface

end Work.Space
