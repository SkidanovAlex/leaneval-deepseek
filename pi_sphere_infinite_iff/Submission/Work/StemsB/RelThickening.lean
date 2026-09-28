import Mathlib
import Submission.Work.Cohomology.localHomology

/-!
# Thickening the second member of a pair does not change relative homology

The workspace's excision (`Work.Cohomology.excision_relChainsMap_isIso`) is stated for **open**
pieces `U`, `A` with `U ∪ A = univ`.  The two-disc decomposition of `Sⁿ` used in Step I of the
sphere-specific route (`CONTRACTS.md` §H) is by **closed** discs whose interiors do not cover the
sphere (the boundary sphere is missed), so the closed-cover form of excision has to be manufactured
from the open one by *thickening*: if `A ↪ B` is a homotopy equivalence then the map of relative
chain complexes `C_*(X,A) → C_*(X,B)` is a quasi-isomorphism.

This file proves exactly that step, in the reusable form: the content is the five lemma applied to
the map of short exact sequences `S(X,A) → S(X,B)` whose first component is the inclusion
`C_*(A) → C_*(B)` and whose second component is the identity — which is
`Work.Cohomology.relChainsMapOf_homologyMap_isIso`, plus `Work.Cohomology.homologyEquiv` for the
hypothesis on the first component.

## Main result

* `Work.StemsB.isIso_relChainsMapOf_of_homotopyEquiv`
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace Work.StemsB

noncomputable section

/-- **Thickening the second member of a pair preserves relative homology (over `ℤ`).**

For `A ⊆ B ⊆ X`, if the inclusion `A → B` is a homotopy equivalence (witnessed by `f`, `g` and the
two homotopies), then the induced map `C_*(X,A) → C_*(X,B)` of relative chain complexes is a
quasi-isomorphism: it induces an isomorphism on homology in every degree. -/
theorem isIso_relChainsMapOf_of_homotopyEquiv {X : TopCat} {A B : Set X}
    (f : TopCat.of A ⟶ TopCat.of B) (g : TopCat.of B ⟶ TopCat.of A)
    (h1 : TopCat.Homotopy (f ≫ g) (𝟙 (TopCat.of A)))
    (h2 : TopCat.Homotopy (g ≫ f) (𝟙 (TopCat.of B)))
    (w : (Work.Cohomology.subtypeIncl X A) ≫ (𝟙 X) =
      f ≫ (Work.Cohomology.subtypeIncl X B))
    (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.relChainsMapOf X X A B (𝟙 X) f w) n) := by
  refine Work.Cohomology.relChainsMapOf_homologyMap_isIso A B (𝟙 X) f w n ?_ ?_
  · intro k
    have hid : Work.Cohomology.chainMap ℤ X X (𝟙 X) =
        𝟙 (Work.Cohomology.singularChains ℤ X) := by
      simp only [Work.Cohomology.chainMap, CategoryTheory.Functor.map_id]
    rw [hid, HomologicalComplex.homologyMap_id]
    infer_instance
  · intro k
    exact Work.Cohomology.homologyEquiv ℤ (TopCat.of A) (TopCat.of B) f g h1 h2 k

end

end Work.StemsB
