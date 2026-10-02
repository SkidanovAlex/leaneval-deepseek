import Mathlib
import Submission.Work.Model.prod_transfer
import Submission.Work.Projective.Model

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `ℂP² × ℂP²` is a smooth `8`-manifold

The product `ℂP² × ℂP²` carries

* the product `ChartedSpace` structure over the product model
  `ModelProd ℝ⁴ ℝ⁴` (`Work.Projective.instChartedSpaceEuclidean 2` on each factor,
  `prodChartedSpace` for the product), and
* the product `IsManifold` structure `(𝓡 4).prod (𝓡 4)` (`IsManifold.prod`).

`Work.Model.prod_transfer` then re-charts this product manifold over the Euclidean model
`ℝ^{4+4} = ℝ^8`, which is the form needed by the rest of the development.

The `abbrev`s below are the two factors' and the product's structures stated over the models
`EuclideanSpace ℝ (Fin 4)` resp. `ModelProd ℝ⁴ ℝ⁴`; they are registered as instances so that the
`IsManifold` product instance and `Work.Model.prod_transfer` can be applied by type-class search.
-/

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace Work.Gen

noncomputable section

open Work.Projective

/-- The Euclidean charted-space structure on `ℂP²`, over the model `EuclideanSpace ℝ (Fin 4)`
(definitionally the `Fin (2 * 2)` of `Work.Projective`). -/
abbrev cp2ChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin 4)) (CP 2) :=
  instChartedSpaceEuclidean 2

attribute [instance] cp2ChartedSpace

/-- The `C^∞` structure on `ℂP²`. -/
abbrev cp2IsManifold : IsManifold (𝓡 4) ∞ (CP 2) :=
  Work.Projective.instIsManifoldEuclidean 2

attribute [instance] cp2IsManifold

/-- The product charted-space structure on `ℂP² × ℂP²`. -/
abbrev cp2cp2ChartedSpace :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 4)) (EuclideanSpace ℝ (Fin 4)))
      (CP 2 × CP 2) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin 4)) (CP 2) (EuclideanSpace ℝ (Fin 4)) (CP 2)

attribute [instance] cp2cp2ChartedSpace

/-- The product `C^∞` structure on `ℂP² × ℂP²`. -/
abbrev cp2cp2IsManifold : IsManifold ((𝓡 4).prod (𝓡 4)) ∞ (CP 2 × CP 2) :=
  IsManifold.prod (CP 2) (CP 2)

attribute [instance] cp2cp2IsManifold

/-- **`ℂP² × ℂP²` is a smooth `8`-manifold.**  The product of the two Euclidean charts of the
factors charts `ℂP² × ℂP²` over `ℝ⁴ × ℝ⁴`, and the model transfer
`Work.Model.prod_transfer` (applied with `m = n = 4`) re-charts it over `ℝ^{4+4} = ℝ^8`. -/
theorem Cp2Cp2Smooth : ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin 8)) (Work.Projective.CP 2 × Work.Projective.CP 2), @IsManifold ℝ _ (EuclideanSpace ℝ (Fin 8)) _ _ (EuclideanSpace ℝ (Fin 8)) _ (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 8))) ((⊤ : ENat) : WithTop ENat) (Work.Projective.CP 2 × Work.Projective.CP 2) _ cs := by
  obtain ⟨c, hc⟩ := Work.Model.prod_transfer (m := 4) (n := 4)
    (M := Work.Projective.CP 2 × Work.Projective.CP 2)
  exact ⟨c, hc⟩

end

end Work.Gen