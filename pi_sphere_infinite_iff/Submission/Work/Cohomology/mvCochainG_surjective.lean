import Mathlib
import Submission.Work.Cohomology.mvCochainDefs

/-!
# Surjectivity of the second map of the cohomological Mayer–Vietoris sequence

The cochain Mayer–Vietoris map
`mvCochainG U V : C^*(U) ⊞ C^*(V) ⟶ C^*(U ∩ V)` is the dual of the chain level map
`(inclUVU_*, inclUVV_*)` (`Work.Cohomology.mvCochainDefs`).  This file proves that it is
degreewise surjective, i.e. that every cochain on `U ∩ V` is the sum of the restrictions of a
cochain on `U` and a cochain on `V`.

The mathematical content is the elementary fact that, for an injective map `p : A → S` of index
sets, the transpose of the induced map `∐_{a : A} R ⟶ ∐_{s : S} R` of coproducts of `R` is
surjective: a functional on the sources extends to a functional on the targets, because `p` has a
retraction (`Function.invFun p`).  The degenerate case `A = ∅` is handled separately, where the
coproduct is an initial object and the target of the transpose is a subsingleton.

## Main results

* `coprodMap_id_eq_identity` — `coprodMap` of the identity is the identity;
* `dualMap_surjective_of_leftInverse` — the transpose of a linear map admitting a left inverse is
  surjective;
* `coprodMap_hom_dualMap_surjective` — the transpose of `coprodMap p` is surjective for `p`
  injective;
* `mvCochainG_surjective` — **the second cohomological Mayer–Vietoris map is degreewise
  surjective**.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- `coprodMap` of the identity map of index types is the identity. -/
lemma coprodMap_id_eq_identity (R : Type) [Ring R] (A : Type) :
    coprodMap (R:=R) (id : A → A) = 𝟙 (∐ (fun _ : A => ModuleCat.of R R)) := by
  rw [coprodMap, Sigma.map'_id, Sigma.map_id]

/-- **The transpose of a linear map admitting a left inverse is surjective.**  If `Q ∘ P = id`
then `dualMap P` has the right inverse `dualMap Q`. -/
lemma dualMap_surjective_of_leftInverse {R : Type} [CommSemiring R] {M N : Type}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (P : M →ₗ[R] N) (Q : N →ₗ[R] M) (h : Q.comp P = LinearMap.id) :
    Function.Surjective (LinearMap.dualMap P) := by
  intro φ
  refine ⟨LinearMap.dualMap Q φ, ?_⟩
  ext x
  rw [LinearMap.dualMap_apply, LinearMap.dualMap_apply]
  have hx : Q (P x) = x := by
    simpa [LinearMap.comp_apply] using LinearMap.congr_fun h x
  rw [hx]

/-- **The transpose of `coprodMap p` is surjective for `p` injective.**  This is the elementary
extension statement: a linear functional on `∐_{a : A} R` extends to `∐_{s : S} R` along the
inclusion `coprodMap p` induced by an injective map of index sets. -/
lemma coprodMap_hom_dualMap_surjective {R : Type} [CommRing R] {A S : Type} (p : A → S)
    (hp : Function.Injective p) :
    Function.Surjective (LinearMap.dualMap ((coprodMap (R:=R) p).hom)) := by
  classical
  rcases isEmpty_or_nonempty A with hA | hA
  · -- If `A` is empty, the source of the transpose is an initial object, so the target of the
    -- transpose is a subsingleton.
    haveI : IsEmpty A := hA
    haveI : Subsingleton (Module.Dual R (∐ (fun _ : A => ModuleCat.of R R) : ModuleCat R)) :=
      ⟨fun u v => by
        have h := Sigma.hom_ext (ModuleCat.ofHom u) (ModuleCat.ofHom v)
          (fun a => isEmptyElim a)
        simpa using congrArg ModuleCat.Hom.hom h⟩
    intro φ
    exact ⟨0, Subsingleton.elim _ _⟩
  · haveI : Nonempty A := hA
    have hgp : Function.invFun p ∘ p = id := funext (Function.leftInverse_invFun hp)
    have hcomp : coprodMap (R:=R) p ≫ coprodMap (R:=R) (Function.invFun p)
        = 𝟙 (∐ (fun _ : A => ModuleCat.of R R)) := by
      rw [coprodMap_comp, hgp, coprodMap_id_eq_identity]
    have hQP : (coprodMap (R:=R) (Function.invFun p)).hom.comp (coprodMap (R:=R) p).hom
        = LinearMap.id := by
      rw [← ModuleCat.hom_comp, hcomp, ModuleCat.hom_id]
    exact dualMap_surjective_of_leftInverse _ _ hQP

/-- **The second cohomological Mayer–Vietoris map is degreewise surjective.** -/
theorem mvCochainG_surjective {X : TopCat} (U V : Set X) (n : ℕ) :
    Function.Surjective (ModuleCat.Hom.hom ((Work.Cohomology.mvCochainG U V).f n)) := by
  -- It suffices to prove surjectivity of the first component of `mvCochainG`, i.e. of the dual of
  -- the chain level inclusion `C_*(U ∩ V) ⟶ C_*(U)`.
  have hsurj : Function.Surjective (ModuleCat.Hom.hom
      ((dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V)))
        (singularChains ℤ (TopCat.of U)) (chainInclU U V)).f n)) := by
    rw [dualComplexMap_f, dualComplexMapComp, ModuleCat.hom_ofHom]
    rw [chainInclU_f]
    exact coprodMap_hom_dualMap_surjective _ (inclUV_injective U V (Opposite.op ⦋n⦌)).1
  intro y
  obtain ⟨α, hα⟩ := hsurj y
  refine ⟨ModuleCat.Hom.hom
    ((biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V).f n) α, ?_⟩
  have h := congrArg (fun (k : (cochainU U V).X n ⟶ (cochainUV U V).X n) =>
      ModuleCat.Hom.hom k α) (mvCochainG_inl U V n)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.trans hα

end

end Work.Cohomology
