import Mathlib
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.CsrSharp.relChainsRHomeomorphCompat

/-!
# The relative chain complex with coefficients in a commutative ring is invariant under a
homeomorphism of pairs

`Work.StemsB.relChainsR R X A = C_*(X, A; R)` is the relative singular chain complex with
coefficients in a commutative ring `R`, defined as the cokernel of the inclusion
`C_*(A;R) ⟶ C_*(X;R)` (`Submission/Work/StemsB/RelChainsR.lean`).

A homeomorphism of pairs `e : X ≃ₜ Y` with `e '' A = B` gives an isomorphism of *chain complexes*
(not merely of homology groups) between `C_*(X,A;R)` and `C_*(Y,B;R)`: the singular chain functor
`TopCat ⥤ ChainComplex (ModuleCat R) ℕ` sends the homeomorphism of the big spaces and the induced
homeomorphism `A ≅ B` of the subspaces to isomorphisms, and these fit into a commutative square
with the two inclusions, so the induced isomorphism of cokernels (`cokernel.mapIso`) is the
desired one.

This is the chain-level strengthening of
`Work.Serre.CsrSharp.relChainsRHomeomorphCompat_gen` (which only records the induced isomorphism on
homology).
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.StemsB

noncomputable section

theorem relChainsRIsoOfHomeo (R : Type) [CommRing R] (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (e : X ≃ₜ Y) (he : ∀ x, x ∈ A ↔ e x ∈ B) :
    Nonempty (Work.StemsB.relChainsR R (TopCat.of X) A ≅ Work.StemsB.relChainsR R (TopCat.of Y) B) := by
  set E := TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) e with hE
  have hEf : ∀ x : X, (E.hom : X → Y) x = e x := by
    intro x
    rw [hE, TopCat.isoOfHomeo_hom, TopCat.ofHom_apply]
    rfl
  have he' : ∀ x, x ∈ A ↔ (E.hom : X → Y) x ∈ B := by
    intro x; rw [hEf x]; exact he x
  have hev : ∀ a : ↥A, (E.hom : X → Y) a.1 ∈ B := fun a => (he' a.1).mp a.2
  have hev' : ∀ b : ↥B, (E.inv : Y → X) b.1 ∈ A := by
    intro b
    refine (he' ((E.inv : Y → X) b.1)).mpr ?_
    have h : (TopCat.Hom.hom E.hom) ((TopCat.Hom.hom E.inv) b.1) = b.1 := by
      have h2 : TopCat.Hom.hom (E.inv ≫ E.hom) = TopCat.Hom.hom (𝟙 (TopCat.of Y)) := by
        rw [E.inv_hom_id]
      exact DFunLike.congr_fun h2 b.1
    rw [h]; exact b.2
  let hA : ↥A ≃ₜ ↥B :=
    { toFun := fun a => ⟨(E.hom : X → Y) a.1, hev a⟩
      invFun := fun b => ⟨(E.inv : Y → X) b.1, hev' b⟩
      left_inv := by
        intro a
        apply Subtype.ext
        have h2 : TopCat.Hom.hom (E.hom ≫ E.inv) = TopCat.Hom.hom (𝟙 (TopCat.of X)) := by
          rw [E.hom_inv_id]
        exact DFunLike.congr_fun h2 a.1
      right_inv := by
        intro b
        apply Subtype.ext
        have h2 : TopCat.Hom.hom (E.inv ≫ E.hom) = TopCat.Hom.hom (𝟙 (TopCat.of Y)) := by
          rw [E.inv_hom_id]
        exact DFunLike.congr_fun h2 b.1
      continuous_toFun := ((TopCat.Hom.hom E.hom).continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := ((TopCat.Hom.hom E.inv).continuous.comp continuous_subtype_val).subtype_mk _ }
  have hsq : Work.StemsB.relChainsRIncl R (TopCat.of X) A ≫
      Work.Cohomology.chainMap R (TopCat.of X) (TopCat.of Y) E.hom =
      Work.Cohomology.chainMap R (TopCat.of ↥A) (TopCat.of ↥B) (TopCat.isoOfHomeo hA).hom ≫
        Work.StemsB.relChainsRIncl R (TopCat.of Y) B := by
    have h2 : (Work.Cohomology.subtypeIncl (TopCat.of X) A ≫ E.hom) =
        ((TopCat.isoOfHomeo hA).hom ≫ Work.Cohomology.subtypeIncl (TopCat.of Y) B) := by
      apply TopCat.hom_ext
      ext a
      rfl
    show Work.Cohomology.chainMap R (TopCat.of ↥A) (TopCat.of X)
        (Work.Cohomology.subtypeIncl (TopCat.of X) A) ≫
        Work.Cohomology.chainMap R (TopCat.of X) (TopCat.of Y) E.hom = _
    rw [← CategoryTheory.Functor.map_comp, h2, CategoryTheory.Functor.map_comp]
  exact ⟨cokernel.mapIso (f := Work.StemsB.relChainsRIncl R (TopCat.of X) A)
    (f' := Work.StemsB.relChainsRIncl R (TopCat.of Y) B)
    (((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).mapIso
      (TopCat.isoOfHomeo hA))
    (((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).mapIso E) hsq⟩

end

end Work.StemsB
