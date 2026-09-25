/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The localisation at a place whose decomposition group contains `U` is injective
(twisted coefficients `μ_p`)

Let `U ≤ Gal(K'/K)` be a subgroup and `A` a place of `K'` over a finite prime of `K`, with
decomposition group `D_A = stabSubgroup A.1`.  If `U ≤ D_A` then the localisation

`H2Twist.loc p U · A : H²(U, μ_p) ⟶ LocalH2Twist p U A.1`

of the twisted (cyclotomic) coefficients `μ_p = Z/p(1)` is injective.  As in the
trivial-coefficient case (`Submission/Work/HassePrinciple/loc_injective_of_le_stabSubgroup.lean`)
the local and the global filtered systems coincide when `U ≤ D_A`: the level groups of `U ⊓ D_A`
and of `U` are the same, and the level module `μ_p(L)` is the *same* module for both, so the
level-wise localisation `locLevel p U A.1 L` is the map induced on `H²` by an isomorphism of
groups with isomorphic coefficient systems, hence injective.  Injectivity on the colimit follows
from the level-wise description of equality in the filtered colimits.

## Main results

* `NK.HasseTwist.map_injective_of_bijective_of_isIso` — general: `groupCohomology.map` along a
  bijective group homomorphism and an isomorphism of coefficient systems is injective;
* `NK.HasseTwist.locCoeff_isIso` — the coefficient morphism of the level-wise localisation is an
  isomorphism (it is the identity on `μ_p(L)`);
* `NK.HasseTwist.locLevel_injective_of_le_stabSubgroup` — `locLevel` is injective;
* `NK.HasseTwist.loc_injective_of_le_stabSubgroup` — the localisation itself is injective.
-/

import Mathlib
import Submission.NK.HasseTwist.Restrict
import Submission.NK.HassePrinciple.loc_injective_of_le_stabSubgroup
import Submission.NK.BrauerTwist.levelMap_locLevel_apply

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

namespace NK.HasseTwist

open CategoryTheory
open NK.BrauerTwist

/-! ## General facts about `groupCohomology.map` -/

section General

variable {k : Type u} [CommRing k] {G H : Type u} [Group G] [Group H]

/-- The map on cohomology induced by a bijective group homomorphism and by the identity morphism
of coefficient systems is an isomorphism: it is the inverse of the isomorphism `mapIso` attached
to the group isomorphism. -/
lemma map_identity_coeff_isIso_of_bijective (f : G →* H) (hf : Function.Bijective f)
    (A : Rep k H) (n : ℕ) :
    IsIso (groupCohomology.map f (𝟙 (Rep.res f A)) n) := by
  let e : G ≃* H := MulEquiv.ofBijective f hf
  have he : ∀ g : G, (LinearEquiv.refl k A.V) ∘ₗ (Rep.res f A).ρ g =
      A.ρ (e g) ∘ₗ (LinearEquiv.refl k A.V) := by
    intro g
    change (A.ρ.comp f) g ∘ₗ (LinearMap.id : A.V →ₗ[k] A.V) =
      A.ρ ((MulEquiv.ofBijective f hf) g) ∘ₗ (LinearMap.id : A.V →ₗ[k] A.V)
    simp only [LinearMap.comp_id]
    rfl
  have hEq : groupCohomology.map f (𝟙 (Rep.res f A)) n =
      (groupCohomology.mapIso (A := A) (B := Rep.res f A) e
        (LinearEquiv.refl k A.V) he n).inv := by
    rw [groupCohomology.mapIso_inv]
    exact (groupCohomology.map_congr rfl (by ext; rfl) n).symm
  rw [hEq]
  infer_instance

/-- **The factorisation of `groupCohomology.map` along the identity of coefficients.**  For a
group homomorphism `f : G →* H` and a coefficient morphism `φ`, the induced map on cohomology is
the composite of the inverse of the "group isomorphism transport" and the map induced by `φ`
with the identity group homomorphism. -/
lemma map_factorization (f : G →* H) {A : Rep k H} {C : Rep k G}
    (φ : Rep.res f A ⟶ C) (n : ℕ) :
    groupCohomology.map f φ n =
      groupCohomology.map f (𝟙 (Rep.res f A)) n ≫
        groupCohomology.map (A := Rep.res f A) (B := C) (MonoidHom.id G) φ n := by
  rw [← groupCohomology.map_comp (f := f) (g := MonoidHom.id G)
      (φ := 𝟙 (Rep.res f A)) (ψ := φ) n]
  exact groupCohomology.map_congr rfl rfl n

/-- **`groupCohomology.map` along a bijective group homomorphism and an isomorphism of coefficient
systems is injective.**  The map factors as an isomorphism (bijectivity of the group homomorphism)
followed by the functorial image of the coefficient morphism, which is an isomorphism because any
functor preserves isomorphisms. -/
lemma map_injective_of_bijective_of_isIso (f : G →* H) (hf : Function.Bijective f)
    {A : Rep k H} {C : Rep k G} (φ : Rep.res f A ⟶ C) (hφ : IsIso φ) (n : ℕ) :
    Function.Injective (groupCohomology.map f φ n).hom := by
  haveI := hφ
  rw [map_factorization f φ n]
  have hX : Function.Injective (groupCohomology.map f (𝟙 (Rep.res f A)) n).hom := by
    haveI := map_identity_coeff_isIso_of_bijective f hf A n
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  have hY : Function.Injective (groupCohomology.map (A := Rep.res f A) (B := C)
      (MonoidHom.id G) φ n).hom := by
    haveI : IsIso (groupCohomology.map (A := Rep.res f A) (B := C) (MonoidHom.id G) φ n) := by
      change IsIso ((groupCohomology.functor k G n).map
        (φ : Rep.res (MonoidHom.id G) (Rep.res f A) ⟶ C))
      infer_instance
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  change Function.Injective ((groupCohomology.map (A := Rep.res f A) (B := C)
    (MonoidHom.id G) φ n).hom ∘ (groupCohomology.map f (𝟙 (Rep.res f A)) n).hom)
  exact hY.comp hX

end General

/-! ## The level-wise localisation with `μ_p`-coefficients -/

section Level

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']

/-- The coefficient inclusion at a fixed level `L` is the identity on `μ_p(L)`. -/
lemma muInclAddHom_refl (p : ℕ) (L : FiniteGaloisIntermediateField K K')
    (x : Additive ↥(muLevel p L)) :
    muInclAddHom (p := p) (L := L) (L' := L) (le_refl L) x = x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [muInclAddHom_apply]
  rfl

/-- The coefficient morphism of the level-wise localisation is an isomorphism: its underlying
linear map is the identity of `μ_p(L)`. -/
lemma locCoeff_isIso (p : ℕ) (U : Subgroup Gal(K'/K)) (A : ValuationSubring K')
    (L : FiniteGaloisIntermediateField K K') : IsIso (locCoeff p U A L) := by
  rw [isIso_iff_mono_and_epi]
  refine ⟨?_, ?_⟩
  · rw [Rep.mono_iff_injective]
    intro x y hxy
    rw [show ⇑(locCoeff p U A L).hom x =
          muInclAddHom (p := p) (L := L) (L' := L) (le_refl L) x from rfl,
        show ⇑(locCoeff p U A L).hom y =
          muInclAddHom (p := p) (L := L) (L' := L) (le_refl L) y from rfl] at hxy
    rw [muInclAddHom_refl p L x, muInclAddHom_refl p L y] at hxy
    exact hxy
  · rw [Rep.epi_iff_surjective]
    intro y
    refine ⟨y, ?_⟩
    rw [show ⇑(locCoeff p U A L).hom y =
          muInclAddHom (p := p) (L := L) (L' := L) (le_refl L) y from rfl,
        muInclAddHom_refl p L y]

/-- If `U ≤ D_A` then the level-wise localisation `locLevel p U A L` is injective: the level
groups of `U ⊓ D_A` and of `U` coincide, so the localisation is induced by an isomorphism of
groups with isomorphic coefficient systems. -/
lemma locLevel_injective_of_le_stabSubgroup (p : ℕ) {U : Subgroup Gal(K'/K)}
    (A : ValuationSubring K') (h : U ≤ NK.BrauerTwist.stabSubgroup A)
    (L : FiniteGaloisIntermediateField K K') :
    Function.Injective (locLevel p U A L) := by
  have hf : Function.Bijective (NK.BrauerHasse.localInclHom U A L) :=
    NK.HassePrinciple.localInclHom_bijective_of_le_stabSubgroup (K := K) (K' := K') A h L
  have hφ : IsIso (locCoeff p U A L) := locCoeff_isIso p U A L
  exact map_injective_of_bijective_of_isIso (NK.BrauerHasse.localInclHom U A L) hf
    (locCoeff p U A L) hφ 2

end Level

/-! ## The localisation on the twisted profinite cohomology -/

theorem loc_injective_of_le_stabSubgroup (p : ℕ) {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] {U : Subgroup Gal(K'/K)}
    (A : NK.BrauerTwist.OverFinitePrime K K')
    (h : U ≤ NK.BrauerTwist.stabSubgroup A.1) :
    Function.Injective
      (fun x : NK.BrauerTwist.H2Twist p U => NK.BrauerTwist.H2Twist.loc p U x A) := by
  intro x y hxy
  obtain ⟨L, a, rfl⟩ := H2Twist.ofLevel_surjective p U x
  obtain ⟨L', b, rfl⟩ := H2Twist.ofLevel_surjective p U y
  simp only [] at hxy
  rw [H2Twist.loc_ofLevel_apply, H2Twist.loc_ofLevel_apply] at hxy
  obtain ⟨M, h₁, h₂, he⟩ := (LocalH2Twist.ofLevel_eq_iff p U A.1 _ _).mp hxy
  rw [← NK.BrauerTwist.levelMap_locLevel_apply p U A.1 h₁ a,
    ← NK.BrauerTwist.levelMap_locLevel_apply p U A.1 h₂ b] at he
  refine (H2Twist.ofLevel_eq_iff p U a b).mpr ⟨M, h₁, h₂, ?_⟩
  exact locLevel_injective_of_le_stabSubgroup p A.1 h M he

end NK.HasseTwist
