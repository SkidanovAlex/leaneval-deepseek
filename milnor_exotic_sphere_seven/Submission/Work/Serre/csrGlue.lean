import Mathlib
import Submission.Work.Serre.csrDefs
import Submission.Work.Cohomology.relChainsMapOf_comp

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Functoriality of the rational pair maps on relative chains

The rational cell step compares several maps of relative chain complexes; the comparisons are all
instances of the functoriality of the construction `(X,A) ↦ C_*(X,A;ℚ)` on maps of pairs.  This
file records that functoriality for `Work.Serre.relChainsRPairMap`, together with the identity case.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- The compatibility of `Work.Serre.csrRelMapOf` with the projections onto the relative chains. -/
theorem cokernel_π_csrRelMapOf {X Y : TopCat} {A : Set X} {B : Set Y} {f : X ⟶ Y}
    {g : TopCat.of A ⟶ TopCat.of B}
    {w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B} :
    cokernel.π (Work.StemsB.relChainsRIncl ℚ X A) ≫ csrRelMapOf X Y A B f g w
      = Work.Cohomology.chainMap ℚ X Y f
        ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ Y B) := by
  unfold csrRelMapOf
  exact Work.Cohomology.cokernel_π_map _ _ _ _ _

/-- Functoriality of `Work.Serre.csrRelMapOf` in a composite of maps of pairs. -/
theorem csrRelMapOf_comp {X Y Z : TopCat} (A : Set X) (B : Set Y) (C : Set Z)
    (f : X ⟶ Y) (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (f' : Y ⟶ Z) (g' : TopCat.of B ⟶ TopCat.of C)
    (w' : Work.Cohomology.subtypeIncl Y B ≫ f' = g' ≫ Work.Cohomology.subtypeIncl Z C)
    (w'' : Work.Cohomology.subtypeIncl X A ≫ (f ≫ f')
      = (g ≫ g') ≫ Work.Cohomology.subtypeIncl Z C) :
    csrRelMapOf X Y A B f g w ≫ csrRelMapOf Y Z B C f' g' w'
      = csrRelMapOf X Z A C (f ≫ f') (g ≫ g') w'' := by
  apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ X A))).1
  calc cokernel.π (Work.StemsB.relChainsRIncl ℚ X A)
        ≫ (csrRelMapOf X Y A B f g w ≫ csrRelMapOf Y Z B C f' g' w')
      = (cokernel.π (Work.StemsB.relChainsRIncl ℚ X A) ≫ csrRelMapOf X Y A B f g w)
          ≫ csrRelMapOf Y Z B C f' g' w' := (Category.assoc _ _ _).symm
    _ = (Work.Cohomology.chainMap ℚ X Y f
          ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ Y B))
          ≫ csrRelMapOf Y Z B C f' g' w' := by rw [cokernel_π_csrRelMapOf]
    _ = Work.Cohomology.chainMap ℚ X Y f
          ≫ (cokernel.π (Work.StemsB.relChainsRIncl ℚ Y B)
              ≫ csrRelMapOf Y Z B C f' g' w') := (Category.assoc _ _ _).symm
    _ = Work.Cohomology.chainMap ℚ X Y f
          ≫ (Work.Cohomology.chainMap ℚ Y Z f'
              ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ Z C)) := by
        rw [cokernel_π_csrRelMapOf]
    _ = (Work.Cohomology.chainMap ℚ X Y f ≫ Work.Cohomology.chainMap ℚ Y Z f')
          ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ Z C) := (Category.assoc _ _ _).symm
    _ = Work.Cohomology.chainMap ℚ X Z (f ≫ f')
          ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ Z C) := by
        rw [Work.Cohomology.chainMap_comp_relChains]
    _ = cokernel.π (Work.StemsB.relChainsRIncl ℚ X A)
          ≫ csrRelMapOf X Z A C (f ≫ f') (g ≫ g') w'' := by
        rw [cokernel_π_csrRelMapOf]

/-- `Work.Serre.csrRelMapOf` of the identity map of pairs is the identity. -/
theorem csrRelMapOf_id (X : TopCat) (A : Set X)
    (w : 𝟙 (TopCat.of A) ≫ Work.Cohomology.subtypeIncl X A
      = Work.Cohomology.subtypeIncl X A ≫ 𝟙 X) :
    csrRelMapOf X X A A (𝟙 X) (𝟙 (TopCat.of A)) w
      = 𝟙 (Work.StemsB.relChainsR ℚ X A) := by
  apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ X A))).1
  rw [Category.comp_id, cokernel_π_csrRelMapOf]
  rw [show Work.Cohomology.chainMap ℚ X X (𝟙 X)
      = 𝟙 (Work.Cohomology.singularChains ℚ X) from by
    simp only [Work.Cohomology.chainMap]
    exact CategoryTheory.Functor.map_id _ _,
    Category.id_comp]

/-- `Work.Serre.relChainsRPairMap` of the identity is the identity. -/
theorem relChainsRPairMap_id (X : Type) [TopologicalSpace X] (A : Set X) :
    relChainsRPairMap A A (ContinuousMap.id X) (by intro x hx; exact hx)
      = 𝟙 (Work.StemsB.relChainsR ℚ (TopCat.of X) A) := by
  unfold relChainsRPairMap
  exact csrRelMapOf_id (TopCat.of X) A (by ext x; rfl)

end

end Work.Serre
