import Mathlib
import Submission.Work.Serre.csrDefs
import Submission.Work.StemsB.SphLoopRelPair
import Submission.Work.Cohomology.relChainsMapOf_comp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A homeomorphism of pairs induces an isomorphism of rational relative chains

`Work.Serre.csrRelMapOf` is the map of relative chain complexes over `ℚ` induced by a map of pairs
`(X,A) → (Y,B)`.  A homeomorphism of pairs `e : X ≃ₜ Y` mapping `A` onto `B` induces an
*isomorphism* of relative chain complexes: both the chain map on the ambient spaces and the one on
the subspaces are isomorphisms (the singular chain functor turns the homeomorphism and its
restriction into mutually inverse chain maps, with no homotopy involved), and a commuting square
whose horizontal maps are isomorphisms induces an isomorphism of the cokernels.

This is the rational analogue of `Work.StemsB.isIso_relChainsMapOf_homeomorph` (coefficients `ℤ`,
`Work.Cohomology.relChainsMapOf`).

It is used by the per-cell comparison `Work.Serre.csrPerCellProved`: the model pair over the
`i`-th open half-ball is compared with the disjoint union of the translated model pairs through
homeomorphisms of pairs, and the transfer of the quasi-isomorphism along such a homeomorphism
needs exactly this statement.
-/

set_option linter.style.haveILetI false

namespace Work.Serre.PerCell

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **A homeomorphism induces an isomorphism of rational singular chain complexes.** -/
theorem isIso_chainMap_sphHomeoHom_rat {X Y : TopCat} (e : X ≃ₜ Y) :
    IsIso (Work.Cohomology.chainMap ℚ X Y (Work.StemsB.sphHomeoHom e)) := by
  refine IsIso.mk ⟨Work.Cohomology.chainMap ℚ Y X (Work.StemsB.sphHomeoHom e.symm), ?_, ?_⟩
  · rw [← Work.Cohomology.chainMap_comp_relChains, Work.StemsB.sphHomeoHom_comp_symm]
    show ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (𝟙 X) = 𝟙 _
    exact CategoryTheory.Functor.map_id _ _
  · rw [← Work.Cohomology.chainMap_comp_relChains, Work.StemsB.sphHomeoHom_symm_comp]
    show ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (𝟙 Y) = 𝟙 _
    exact CategoryTheory.Functor.map_id _ _

/-- **The restriction of a homeomorphism of pairs induces an isomorphism of rational chain
complexes.** -/
theorem isIso_chainMap_pairRestrict_rat {X Y : TopCat} (e : X ≃ₜ Y) {A : Set X} {B : Set Y}
    (hAB : ∀ x ∈ A, Work.StemsB.sphHomeoHom e x ∈ B)
    (hBA : ∀ y ∈ B, Work.StemsB.sphHomeoHom e.symm y ∈ A) :
    IsIso (Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B)
      (Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e) A B hAB)) := by
  have h1 : Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e) A B hAB
      ≫ Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e.symm) B A hBA
      = 𝟙 (TopCat.of A) := by
    apply TopCat.hom_ext
    ext a
    exact e.symm_apply_apply a.1
  have h2 : Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e.symm) B A hBA
      ≫ Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e) A B hAB
      = 𝟙 (TopCat.of B) := by
    apply TopCat.hom_ext
    ext b
    exact e.apply_symm_apply b.1
  refine IsIso.mk ⟨Work.Cohomology.chainMap ℚ (TopCat.of B) (TopCat.of A)
      (Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e.symm) B A hBA), ?_, ?_⟩
  · rw [← Work.Cohomology.chainMap_comp_relChains, h1]
    show ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (𝟙 (TopCat.of A)) = 𝟙 _
    exact CategoryTheory.Functor.map_id _ _
  · rw [← Work.Cohomology.chainMap_comp_relChains, h2]
    show ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map (𝟙 (TopCat.of B)) = 𝟙 _
    exact CategoryTheory.Functor.map_id _ _

/-- **A homeomorphism of pairs induces an isomorphism of rational relative chain complexes.**

This is `Work.Serre.csrRelMapOf` for the map of pairs given by a homeomorphism `e : X ≃ₜ Y` and
membership conditions `hAB`, `hBA` (there is no need for an explicit biconditional: the two
implications together with the homeomorphism property already make the map of pairs an
isomorphism). -/
theorem isIso_csrRelMapOf_homeo {X Y : TopCat.{0}} (e : X ≃ₜ Y) (A : Set X) (B : Set Y)
    (hAB : ∀ x ∈ A, Work.StemsB.sphHomeoHom e x ∈ B)
    (hBA : ∀ y ∈ B, Work.StemsB.sphHomeoHom e.symm y ∈ A)
    (w : CategoryTheory.CategoryStruct.comp (Work.Cohomology.subtypeIncl X A)
          (Work.StemsB.sphHomeoHom e)
        = CategoryTheory.CategoryStruct.comp
            (Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e) A B hAB)
            (Work.Cohomology.subtypeIncl Y B)) :
    CategoryTheory.IsIso (Work.Serre.csrRelMapOf X Y A B (Work.StemsB.sphHomeoHom e)
      (Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e) A B hAB) w) := by
  haveI hq : IsIso (Work.Cohomology.chainMap ℚ X Y (Work.StemsB.sphHomeoHom e)) :=
    isIso_chainMap_sphHomeoHom_rat e
  haveI hp : IsIso (Work.Cohomology.chainMap ℚ (TopCat.of A) (TopCat.of B)
      (Work.StemsB.pairRestrict (Work.StemsB.sphHomeoHom e) A B hAB)) :=
    isIso_chainMap_pairRestrict_rat e hAB hBA
  unfold Work.Serre.csrRelMapOf
  exact inferInstance

end

end Work.Serre.PerCell
