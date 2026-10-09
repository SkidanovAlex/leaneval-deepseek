import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.detectorInterface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Sha2Lib

/-- **The counit of the induction adjunction `Ind_N^G ⊣ res_N` is surjective.**

For a group `G`, a subgroup `N ≤ G` and any `G`-module `M` (spelled `Rep Coeff G`), the counit
`ε : Ind_N^G (res_N M) ⟶ M` of Mathlib's adjunction `Rep.indResAdjunction Coeff N.subtype` is
surjective on underlying sets.

This is the `hc : Function.Surjective c.hom` hypothesis of the proved
`Work.SSGRoute.Sha2Lib.detectsAt_of_coeff_surjection`, which the C6 route
(`_lead_design/ssg_pt_design_1002/DESIGN.md` §2, step 2) uses with `N` = the normal closure of the
inertia at `q` and `c := ε : Ind_N^{Gal(K/k)}(res_N M) ⟶ M` to move detection from the cover to `M`;
the pullback brick `Work.Sha2Lib.ext_comp_mk0_ne_zero_of_surjective` (proved) supplies the other half.

Both reviewers located the short proof and confirmed the statement: in Mathlib
`Rep.ind φ A = (k[H] ⊗ₖ A)_G`, `indResAdjunction` is `Adjunction.mkOfHomEquiv` with
`indResHomEquiv.toFun f = f.hom ∘ₗ IndV.mk φ A.ρ 1`, and `counit.app M` is
`(indResHomEquiv _ M).symm 𝟙`, so `right_inv` gives `(counit.app M).hom ∘ IndV.mk 1 = 𝟙` and hence
`ε.hom ⟦1 ⊗ m⟧ = m` for every `m : M`: the map is onto, with the explicit section `m ↦ ⟦1 ⊗ m⟧`.
So the proof is short: **do not spend hours here.**  `[N.FiniteIndex]` is not needed by the proof
(the claim holds for every subgroup) but is kept since `N` in the application is a subgroup of the
finite group `Gal(K/k)`.

Caveat from review: the straightforward proof uses
`Representation.IndV.mk N.subtype (Rep.res N.subtype M).ρ 1`, and instance search on
`Module Coeff (Rep.res N.subtype M).V` may synthesize a `ULift.module`-path instance not defeq to
the one the statement uses, giving a "synthesized instance is not definitionally equal" error; pin
the instance (`letI`/`haveI` with the intended `Module` structure) or go through
`Rep.epi_iff_surjective`.  `Sha2Lib.isUnramifiedDetector_of_induced` uses the right triangle identity
`η ≫ Rep.resMap N.subtype ε = 𝟙` of this same adjunction, so the API is available. -/
theorem indRes_counit_surjective {G : Type} [Group G] (N : Subgroup G) [N.FiniteIndex]
    (M : Rep.{0} SSGRoute.PTExt.Coeff G) :
    Function.Surjective
      ((Rep.indResAdjunction SSGRoute.PTExt.Coeff N.subtype).counit.app M).hom := by
  -- It suffices to show that the counit is an epimorphism in `Rep Coeff G`.
  refine (Rep.epi_iff_surjective _).1 ?_
  refine CategoryTheory.Epi.mk ?_
  -- Under the hom-equivalence of the adjunction, the counit is the identity of `res N.subtype M`.
  have key : (Rep.indResAdjunction SSGRoute.PTExt.Coeff N.subtype).homEquiv
        (Rep.res N.subtype M) ((CategoryTheory.Functor.id _).obj M)
        ((Rep.indResAdjunction SSGRoute.PTExt.Coeff N.subtype).counit.app M)
      = CategoryTheory.CategoryStruct.id (Rep.res N.subtype M) := by
    rw [Rep.indResAdjunction, CategoryTheory.Adjunction.mkOfHomEquiv_counit_app,
      CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv]
    exact Equiv.apply_symm_apply _ _
  intro Z g h hgh
  -- Naturality of `homEquiv` turns `ε ≫ g = ε ≫ h` into `res g = res h`.
  have h1 : (Rep.indResAdjunction SSGRoute.PTExt.Coeff N.subtype).homEquiv
        (Rep.res N.subtype M) Z
        (CategoryTheory.CategoryStruct.comp
          ((Rep.indResAdjunction SSGRoute.PTExt.Coeff N.subtype).counit.app M) g)
      = (Rep.resFunctor N.subtype).map g := by
    rw [CategoryTheory.Adjunction.homEquiv_naturality_right (X := Rep.res N.subtype M), key]
    simp
  have h2 : (Rep.indResAdjunction SSGRoute.PTExt.Coeff N.subtype).homEquiv
        (Rep.res N.subtype M) Z
        (CategoryTheory.CategoryStruct.comp
          ((Rep.indResAdjunction SSGRoute.PTExt.Coeff N.subtype).counit.app M) h)
      = (Rep.resFunctor N.subtype).map h := by
    rw [CategoryTheory.Adjunction.homEquiv_naturality_right (X := Rep.res N.subtype M), key]
    simp
  have h3 : (Rep.resFunctor N.subtype).map g = (Rep.resFunctor N.subtype).map h := by
    rw [← h1, ← h2, hgh]
  -- The restriction functor is faithful.
  exact CategoryTheory.Functor.Faithful.map_injective h3

end Work.Sha2Lib
