import Mathlib
import Submission.Work.Cohomology.localHomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Relative homology is invariant under a homeomorphism of pairs (compat copy)

A self-contained transplant of `Work.Cohomology.relChains_homeomorph`
(`Submission/Work/Cohomology/localCohomology.lean`) that does not import
`Submission.Work.Cohomology.localCohomology` (whose declaration `Work.Cohomology.dualZ` clashes
with the identically named declaration of `Submission.Work.Cohomology.dualZ`, making the two
modules impossible to import together).

If `e : X ≃ₜ Y` carries the subset `A ⊆ X` onto `B ⊆ Y`, then it induces an isomorphism
`H_k(X, A) ≅ H_k(Y, B)` of relative singular homology groups.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-- **Relative homology is invariant under a homeomorphism of pairs**: if `e : X ≃ₜ Y` maps `A`
onto `B`, then `H_k(X, A) ≅ H_k(Y, B)`. -/
theorem relChainsHomeomorphCompat (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (e : X ≃ₜ Y) (he : ∀ x, x ∈ A ↔ e x ∈ B) (k : ℕ) :
    Nonempty ((relChains (TopCat.of X) A).homology k ≅ (relChains (TopCat.of Y) B).homology k) := by
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
  have hsq : inclChains (TopCat.of X) A ≫ chainMap ℤ (TopCat.of X) (TopCat.of Y) E.hom =
      chainMap ℤ (TopCat.of ↥A) (TopCat.of ↥B) (TopCat.isoOfHomeo hA).hom ≫
        inclChains (TopCat.of Y) B := by
    have h2 : (subtypeIncl (TopCat.of X) A ≫ E.hom) =
        ((TopCat.isoOfHomeo hA).hom ≫ subtypeIncl (TopCat.of Y) B) := by
      apply TopCat.hom_ext
      ext a
      rfl
    show chainMap ℤ (TopCat.of ↥A) (TopCat.of X) (subtypeIncl (TopCat.of X) A) ≫
        chainMap ℤ (TopCat.of X) (TopCat.of Y) E.hom = _
    rw [← CategoryTheory.Functor.map_comp, h2, CategoryTheory.Functor.map_comp]
  exact ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k).mapIso
    (cokernel.mapIso (f := inclChains (TopCat.of X) A) (f' := inclChains (TopCat.of Y) B)
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso
        (TopCat.isoOfHomeo hA))
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso E) hsq)⟩

end

end Work.Cohomology
