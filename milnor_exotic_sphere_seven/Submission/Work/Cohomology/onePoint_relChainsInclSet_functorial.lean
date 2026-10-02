import Mathlib
import Submission.Work.Cohomology.localHomology_top_free_onePoint
import Submission.Work.Cohomology.onePointSpace_compl_point_homeo

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Functoriality of the inclusion of relative chain complexes towards a punctured sphere

For a subset `U ⊆ OnePoint ℝ^N` not containing a point `pt`, the inclusion of the *excluded* sets
`U ⊆ {pt}ᶜ` induces a map of relative chain complexes
`relChainsInclSet : C_*(X, U) ⟶ C_*(X, {pt}ᶜ)`.

The point of this file is the compatibility of that map with the projections
`C_*(X) ⟶ C_*(X, A) = cokernel (C_*(A) ⟶ C_*(X))`: at the level of chain complexes

`cokernel.π (inclChains X U) ≫ relChainsInclSet X h = cokernel.π (inclChains X {pt}ᶜ)`,

because `relChainsInclSet X h` is by definition the map of cokernels induced by the identity of `X`,
and `chainMap ℤ X X (𝟙 X) = 𝟙`.  Applying the homology functor gives the statement below.
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.Cohomology

open CategoryTheory CategoryTheory.Limits

/-- The projection to the relative chain complex is compatible with the map of relative chain
complexes induced by an inclusion `A ⊆ B` of the excluded sets: on `C_*(X)` the two ways of going
to `C_*(X,B)` agree. -/
theorem relChainsInclSet_comp_cokernel_π {X : TopCat.{0}} {A B : Set X} (h : A ⊆ B) :
    cokernel.π (inclChains X A) ≫ relChainsInclSet X h = cokernel.π (inclChains X B) := by
  rw [relChainsInclSet, relChainsMapOf]
  rw [cokernel_π_map]
  rw [chainMap_id' X, Category.id_comp]

theorem onePoint_relChainsInclSet_functorial {N : ℕ}
    (U : Set (OnePoint (EuclideanSpace ℝ (Fin N)))) (pt : OnePoint (EuclideanSpace ℝ (Fin N)))
    (hpt : pt ∉ U) :
    CategoryTheory.CategoryStruct.comp
      (HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
          (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin N)))) U)) N)
      (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsInclSet (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin N))))
          (Set.subset_compl_singleton_iff.mpr hpt)) N)
    = HomologicalComplex.homologyMap
        (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
          (TopCat.of (OnePoint (EuclideanSpace ℝ (Fin N))))
          ({pt}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin N)))))) N := by
  have hchain := relChainsInclSet_comp_cokernel_π
    (X := TopCat.of (OnePoint (EuclideanSpace ℝ (Fin N)))) (A := U)
    (B := ({pt}ᶜ : Set (OnePoint (EuclideanSpace ℝ (Fin N)))))
    (Set.subset_compl_singleton_iff.mpr hpt)
  rw [← HomologicalComplex.homologyMap_comp, hchain]

end Work.Cohomology
