import Mathlib
import Submission.Work.Cohomology.localHomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Cohomology

open CategoryTheory CategoryTheory.Limits

/-- Functoriality of `chainMap` on singular chains, in the form used below. -/
lemma chainMap_comp_relChains (R : Type) [CommRing R] {X Y Z : TopCat} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    chainMap R X Z (f ≫ g) = chainMap R X Y f ≫ chainMap R Y Z g := by
  simp only [chainMap, Functor.map_comp]

theorem relChainsMapOf_comp {X Y Z : TopCat} (A : Set X) (B : Set Y) (C : Set Z)
    (f : X ⟶ Y) (g : TopCat.of A ⟶ TopCat.of B)
    (w : Work.Cohomology.subtypeIncl X A ≫ f = g ≫ Work.Cohomology.subtypeIncl Y B)
    (f' : Y ⟶ Z) (g' : TopCat.of B ⟶ TopCat.of C)
    (w' : Work.Cohomology.subtypeIncl Y B ≫ f' = g' ≫ Work.Cohomology.subtypeIncl Z C)
    (w'' : Work.Cohomology.subtypeIncl X A ≫ (f ≫ f')
      = (g ≫ g') ≫ Work.Cohomology.subtypeIncl Z C) :
    Work.Cohomology.relChainsMapOf X Y A B f g w ≫ Work.Cohomology.relChainsMapOf Y Z B C f' g' w'
      = Work.Cohomology.relChainsMapOf X Z A C (f ≫ f') (g ≫ g') w'' := by
  unfold relChainsMapOf
  -- Two morphisms out of the cokernel `relChains X A` are equal as soon as their
  -- precompositions with the epimorphism `cokernel.π (inclChains X A)` agree.
  apply (cancel_epi (cokernel.π (inclChains X A))).1
  -- Move the projection across the composite and evaluate it on both cokernel maps.
  rw [← Category.assoc, cokernel_π_map, Category.assoc, cokernel_π_map, cokernel_π_map]
  -- What remains is precisely functoriality of `chainMap` on the `X ⟶ Y ⟶ Z` factor.
  rw [← Category.assoc, chainMap_comp_relChains]

end Work.Cohomology
