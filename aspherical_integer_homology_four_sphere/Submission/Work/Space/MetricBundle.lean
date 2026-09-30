/-
# The `C^∞` Riemannian bundle of a model atlas

Once the transitions of the model atlas are isometries (`Work.Space.ModelAtlas.Isometry`, a class),
the metric `A.gM` of `Work.Space.Metric` is smooth: the section of the hom-bundle
`y ↦ (A.gM.inner y)` is `C^∞` by `Work.Space.ModelAtlas.contMDiff_inner`.  This file packages that
into the two instances the rest of the project uses:

* `Work.Space.ModelAtlas.contMDiffMetric` — the `Bundle.ContMDiffRiemannianMetric`;
* `Work.Space.ModelAtlas.instIsContMDiffRiemannianBundle` — the
  `IsContMDiffRiemannianBundle I4 ∞ E4 (fun y ↦ TangentSpace I4 y)` instance.
-/
import Mathlib
import Submission.Work.Space.ModelAtlas.contMDiff_inner

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open scoped Manifold ContDiff Topology Bundle
open Bundle

namespace Work.Space

namespace ModelAtlas

variable {M : Type*} [TopologicalSpace M] [A : ModelAtlas M] [ChartedSpace E4 M]
  [IsManifold I4 ∞ M] [A.HasIsometry]

/-- **The `C^∞` Riemannian metric of a model atlas.** -/
noncomputable def contMDiffMetric :
    Bundle.ContMDiffRiemannianMetric I4 (((⊤ : ℕ∞) : WithTop ℕ∞)) E4
      (fun y : M => TangentSpace I4 y) where
  inner := A.gM.inner
  symm := A.gM.symm
  pos := A.gM.pos
  isVonNBounded := A.gM.isVonNBounded
  contMDiff := contMDiff_inner A (ModelAtlas.HasIsometry.out (A := A))

/-- **The metric of a model atlas is a smooth Riemannian bundle.** -/
instance instIsContMDiffRiemannianBundle :
    IsContMDiffRiemannianBundle I4 (((⊤ : ℕ∞) : WithTop ℕ∞)) E4
      (fun y : M => TangentSpace I4 y) :=
  ⟨A.gM.inner, contMDiff_inner A (ModelAtlas.HasIsometry.out (A := A)), fun _ _ _ => rfl⟩

end ModelAtlas

end Work.Space
