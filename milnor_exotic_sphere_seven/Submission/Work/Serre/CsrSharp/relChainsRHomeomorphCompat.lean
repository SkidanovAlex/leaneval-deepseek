import Mathlib
import Submission.Work.StemsB.RelChainsR

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Relative homology with coefficients in a commutative ring is invariant under a homeomorphism
of pairs

`Work.StemsB.relChainsR R X A = C_*(X, A; R)` is the relative singular chain complex with
coefficients in a commutative ring `R` (the cokernel of the inclusion `C_*(A;R) ⟶ C_*(X;R)`).

This file proves that a homeomorphism of pairs `e : X ≃ₜ Y` with `e '' A = B` induces an
isomorphism `H_k(X, A; R) ≅ H_k(Y, B; R)`, by transporting the short exact sequences
`0 → C_*(A;R) → C_*(X;R) → C_*(X,A;R) → 0` along `e`.  The argument is coefficient-independent,
so we prove the general `R` version `relChainsRHomeomorphCompat_gen` and specialise to `R = ℚ`,
which is the requested statement.

The `ℤ`-coefficient version of the same argument is
`Work.Cohomology.relChainsHomeomorphCompat`.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Serre.CsrSharp

noncomputable section

/-- **Relative singular homology with coefficients in an arbitrary commutative ring is invariant
under a homeomorphism of pairs.**  If `e : X ≃ₜ Y` maps `A ⊆ X` onto `B ⊆ Y`, then
`H_k(X, A; R) ≅ H_k(Y, B; R)`. -/
theorem relChainsRHomeomorphCompat_gen (R : Type) [CommRing R] (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (A : Set X) (B : Set Y) (e : X ≃ₜ Y)
    (he : ∀ x, x ∈ A ↔ e x ∈ B) (k : ℕ) :
    Nonempty ((Work.StemsB.relChainsR R (TopCat.of X) A).homology k ≅
      (Work.StemsB.relChainsR R (TopCat.of Y) B).homology k) := by
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
  exact ⟨(HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) k).mapIso
    (cokernel.mapIso (f := Work.StemsB.relChainsRIncl R (TopCat.of X) A)
      (f' := Work.StemsB.relChainsRIncl R (TopCat.of Y) B)
      (((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).mapIso
        (TopCat.isoOfHomeo hA))
      (((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).mapIso E) hsq)⟩

/-- **Relative singular homology with rational coefficients is invariant under a homeomorphism of
pairs**: if `e : X ≃ₜ Y` maps `A ⊆ X` onto `B ⊆ Y`, then `H_k(X, A; ℚ) ≅ H_k(Y, B; ℚ)`. -/
theorem relChainsRHomeomorphCompat (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (e : X ≃ₜ Y) (he : ∀ x, x ∈ A ↔ e x ∈ B) (k : ℕ) :
    Nonempty ((Work.StemsB.relChainsR ℚ (TopCat.of X) A).homology k ≅
      (Work.StemsB.relChainsR ℚ (TopCat.of Y) B).homology k) :=
  relChainsRHomeomorphCompat_gen ℚ X Y A B e he k

end

end Work.Serre.CsrSharp
