/-
# The chain level identity expressing the restriction–coind counit

This file proves the chain level identity

`ι_{coind A} ≫ λ⁻¹ ≫ ψ = cochainsMap S.subtype (counit.app A) ≫ ι_A`

where

* `ι_A : inhomogeneousCochains A ≅ Hom(bar_S, A)` is the comparison isomorphism of
  inhomogeneous cochains with `Hom(bar, -)` (`groupCohomology.inhomogeneousCochainsIso`),
* `λ : Hom(Res(bar_G), A) ≅ Hom(bar_G, coind A)` is the isomorphism underlying Shapiro's lemma
  (`NK.RepresentationTheory.GroupCohomology.lambdaIso`),
* `ψ : Hom(Res(bar_G), A) ⟶ Hom(bar_S, A)` is induced by the canonical chain map
  `bar_S ⟶ Res(bar_G)` (`NK.RepresentationTheory.GroupCohomology.psiMap`),
* and the counit of the restriction–coind adjunction is the comparison on the other side.

Writing `M = coind S.subtype A`, both sides are maps `C•(G, M) ⟶ Hom(bar_S, A)`.  On the level of
elements the identity is the tautology `(z (S.subtype ∘ x)) 1 = (z (S.subtype ∘ x)) 1`: the left
hand side is the value of `ψ ∘ λ⁻¹ ∘ ι` at a cochain, and the two auxiliary lemmas below compute
each of the two composites at the basis element `single x (single 1 1)` of the `i`-th chains of `S`.
-/
import Mathlib
import Submission.NK.RepresentationTheory.GroupCohomology.res_counit_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.RepresentationTheory.GroupCohomology

open CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false in
/-- The left hand side of `key_chain_identity_counit` evaluated at a cochain `z` and at the basis
element of `(bar_S).X i` indexed by `x : Fin i → S`.  The value is `(z (S.subtype ∘ x)) 1`. -/lemma key_chain_identity_counit_lhs_apply {k : Type} [CommRing k] {G : Type} [Group G]
    (S : Subgroup G) (A : Rep.{0,0,0} k S) (i : ℕ)
    (z : ↑((groupCohomology.inhomogeneousCochains (Rep.coind S.subtype A)).X i)) (x : Fin i → S) :
    (Rep.Hom.hom (ModuleCat.Hom.hom ((psiMap k G S A).f i)
      (ModuleCat.Hom.hom ((lambdaIso k G S A).symm.hom.f i)
        (ModuleCat.Hom.hom
          ((groupCohomology.inhomogeneousCochainsIso (Rep.coind S.subtype A)).hom.f i) z))))
      (Finsupp.single x (MonoidAlgebra.single 1 1)) =
    (Representation.coindV S.subtype A.ρ).subtype (z (S.subtype ∘ x)) 1 := by
  rw [psiMap_apply, lambdaIso_symm_apply, barResChain_f_apply, inhomogeneousCochainsIso_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The right hand side of `key_chain_identity_counit` evaluated at a cochain `z` and at the basis
element of `(bar_S).X i` indexed by `x : Fin i → S`.  The value is `(z (S.subtype ∘ x)) 1`, as for
the left hand side. -/lemma key_chain_identity_counit_rhs_apply {k : Type} [CommRing k] {G : Type} [Group G]
    (S : Subgroup G) (A : Rep.{0,0,0} k S) (i : ℕ)
    (z : ↑((groupCohomology.inhomogeneousCochains (Rep.coind S.subtype A)).X i)) (x : Fin i → S) :
    (Rep.Hom.hom (ModuleCat.Hom.hom ((groupCohomology.inhomogeneousCochainsIso A).hom.f i)
      (ModuleCat.Hom.hom
        ((groupCohomology.cochainsMap S.subtype
          ((Rep.resCoindAdjunction k S.subtype).counit.app A)).f i) z)))
      (Finsupp.single x (MonoidAlgebra.single 1 1)) =
    (Representation.coindV S.subtype A.ρ).subtype (z (S.subtype ∘ x)) 1 := by
  rw [inhomogeneousCochainsIso_apply, groupCohomology.cochainsMap_f_hom]
  show (Rep.Hom.hom ((Rep.resCoindAdjunction k S.subtype).counit.app A)) (z (S.subtype ∘ x)) =
    (Representation.coindV S.subtype A.ρ).subtype (z (S.subtype ∘ x)) 1
  rw [counit_app_apply]

set_option backward.isDefEq.respectTransparency false in
/-- Chain-level identity: the comparison `ι ≫ λ⁻¹ ≫ ψ` coincides with the map induced by the
counit of the restriction–coind adjunction. -/
theorem key_chain_identity_counit {k : Type} [CommRing k] {G : Type} [Group G] (S : Subgroup G) (A : Rep.{0,0,0} k S) : CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp (groupCohomology.inhomogeneousCochainsIso (Rep.coind S.subtype A)).hom (NK.RepresentationTheory.GroupCohomology.lambdaIso k G S A).symm.hom) (NK.RepresentationTheory.GroupCohomology.psiMap k G S A) = CategoryTheory.CategoryStruct.comp (groupCohomology.cochainsMap S.subtype ((Rep.resCoindAdjunction k S.subtype).counit.app A)) (groupCohomology.inhomogeneousCochainsIso A).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  ext z
  apply Rep.free_ext k S A
  intro x
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
  exact Eq.trans (key_chain_identity_counit_lhs_apply S A i z x)
    (key_chain_identity_counit_rhs_apply S A i z x).symm

end NK.RepresentationTheory.GroupCohomology
