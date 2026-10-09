import Mathlib
import Submission.NK.HassePrinciple.CyclicBase
import Submission.NK.HassePrinciple.ideleClassGroupH1Pgroup
import Submission.NK.HassePrinciple.repIso_quotientToInvariants_fixedField
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_eq_of_fundamental_class
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

namespace NK.HassePrinciple

variable {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]

/-- **`H¹(S, C_E) = 0` for a `q`-subgroup `S ≤ Gal(E/F)`** of a finite Galois extension of number
fields, from the licensed cyclic input.

The subgroup `S` is *not* assumed normal in `Gal(E/F)`: what matters is that `E ⧸ E^S` is Galois
with group `S` (`E^{Gal(E/E^S)} = E^S`, the fundamental theorem of finite Galois theory, which
needs no normality), so the proved `p`-group case
`NK.HassePrinciple.subsingleton_groupCohomology_one_ideleClassGroup_of_isPGroup` applies to the
extension `E ⧸ E^S` of number fields, and the result is transported along the equivariant
identification `Gal(E/E^S) ≅ S`. -/
theorem subsingleton_groupCohomology_one_res_ideleClassGroup_of_isPGroup
    (h : CyclicHasseInput) (q : ℕ) (hq : Nat.Prime q)
    (S : Subgroup (E ≃ₐ[F] E)) (hS : IsPGroup q S) :
    Subsingleton (groupCohomology
      (Rep.res S.subtype (NK.GlobalCFT.IdeleClassGroup.rep F E)) 1) := by
  classical
  let K : IntermediateField F E := IntermediateField.fixedField S
  haveI : NumberField ↥K := inferInstance
  haveI : FiniteDimensional ↥K E := inferInstance
  haveI : IsGalois ↥K E := inferInstance
  have hKpg : IsPGroup q (E ≃ₐ[↥K] E) :=
    IsPGroup.of_equiv hS (IntermediateField.subgroupEquivAlgEquiv S)
  have hin : CyclicInput q := ⟨hq, h.hasse_norm, h.herbrand⟩
  have hK : Subsingleton (groupCohomology (NK.GlobalCFT.IdeleClassGroup.rep ↥K E) 1) :=
    subsingleton_groupCohomology_one_ideleClassGroup_of_isPGroup hin hKpg
  haveI : Subsingleton (groupCohomology (NK.GlobalCFT.IdeleClassGroup.rep ↥K E) 1) := hK
  exact ((groupCohomology.mapIso (G := ↥S) (H := (E ≃ₐ[↥K] E))
      (A := NK.GlobalCFT.IdeleClassGroup.rep ↥K E)
      (B := Rep.res S.subtype (NK.GlobalCFT.IdeleClassGroup.rep F E))
      (IntermediateField.subgroupEquivAlgEquiv S) (LinearEquiv.refl ℤ _)
      (by intro g; rfl) 1).toLinearEquiv).injective.subsingleton

set_option maxHeartbeats 1600000 in
/-- **`H¹(Γ, C_E) = 0` for every finite Galois extension of number fields**, from the licensed
cyclic input (`NK.HassePrinciple.CyclicHasseInput` = the Hasse norm result + the Herbrand
quotient for *cyclic* extensions).

This is the classical second inequality / field axiom for the idèle class group.  Reduction plan:

* the cyclic case is the proved `NK.HassePrinciple.subsingleton_tateCohomology_one_of_cyclic`
  (index formula + Herbrand quotient + the on-disk `H⁰`-computation);
* the `ℓ`-group case is the proved
  `NK.HassePrinciple.subsingleton_groupCohomology_one_ideleClassGroup_of_isPGroup`
  (strong induction on the order, inflation–restriction in degree 1, `H1InfRes_exact`, and the
  equivariant identification `C_E^N ≅ C_{E^N}` of `repIso_quotientToInvariants_fixedField`);
* the general case follows from the `ℓ`-group case by restriction to Sylow subgroups: if
  `S ≤ Γ` then `cores_{S}^{Γ} ∘ res_{Γ}^{S}` is multiplication by the index `[Γ : S]`, so
  `res_{S}(x) = 0` implies `[Γ : S] · x = 0`.  Applying this to a Sylow `ℓ`-subgroup for every
  prime `ℓ` gives that the order of `x` divides `[Γ : S_ℓ]` for all `ℓ`; for `q | ord x` the choice
  `ℓ = q` then gives the contradiction `q ∣ [Γ : S_q]` with `[Γ : S_q]` prime to `q`.  Hence
  `x = 0`.

Note on the Sylow step: for *any* subgroup `S ≤ Gal(E/F)` of a finite Galois extension, the
extension `E ⧸ E^S` is Galois with group `S` (`E^{Gal(E/E^S)} = E^S`; the fundamental result of
finite Galois theory needs no normality of `S` — normality is only needed for `E^S/F`), so the
`ℓ`-group result applies verbatim to `E ⧸ E^S` with base field `E^S`.  The transfer identity
`cores ∘ res = [Γ : S]` in degree one can be proved at the level of cocycles if Mathlib's
corestriction is unavailable (the cocycle-level transfer apparatus of
`Submission/Work/HassePrinciple/H2_map_injective_of_coprime_index.lean` is the degree-two model).

An alternative route to the same conclusion, avoiding corestriction entirely: use the
inflation–restriction sequence in degree one, `H¹(Γ ⧸ N, C_E^N) → H¹(Γ, C_E) → H¹(N, C_E)`, by
strong induction on `Nat.card Γ` over a composition series (`Γ ⧸ N` of prime order; the quotient
side is the cyclic case transported along `C_E^N ≅ C_{E^N}`), together with the Sylow argument
only for the simple non-cyclic groups. -/
theorem subsingleton_groupCohomology_one_ideleClassGroup_all
    (h : NK.HassePrinciple.CyclicHasseInput) {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] :
    Subsingleton (groupCohomology (NK.GlobalCFT.IdeleClassGroup.rep F E) 1) := by
  classical
  set M : Rep.{0,0,0} ℤ (E ≃ₐ[F] E) := NK.GlobalCFT.IdeleClassGroup.rep F E with hM
  suffices hmain : ∀ x : groupCohomology M 1, x = 0 from
    ⟨fun x y => by rw [hmain x, hmain y]⟩
  -- the corestriction identity in degree one: restriction to `S` vanishes ⟹ `[Γ : S] • x = 0`
  have hcor_res : ∀ (S : Subgroup (E ≃ₐ[F] E)) (x : groupCohomology M 1),
      Subsingleton (groupCohomology (Rep.res S.subtype M) 1) → S.index • x = 0 := by
    intro S x hS
    have hc := NU.cor_resNatTrans_comp_apply S M 1 x
    have h2 : (NU.cor S M 1)
        (ConcreteCategory.hom ((groupCohomology.resNatTrans ℤ (G := ↥S) (H := E ≃ₐ[F] E)
          S.subtype 1).app M) x) = S.index • x :=
      show (ConcreteCategory.hom ((groupCohomology.resNatTrans ℤ (G := ↥S) (H := E ≃ₐ[F] E)
          S.subtype 1).app M ≫ NU.cor S M 1)) x = S.index • x from hc
    have hz : ConcreteCategory.hom ((groupCohomology.resNatTrans ℤ (G := ↥S) (H := E ≃ₐ[F] E)
        S.subtype 1).app M) x = 0 := hS.elim _ _
    rw [← h2, hz]
    change (NU.cor S M 1).hom 0 = 0
    simp
  -- (i) the order `|Γ|` of the Galois group annihilates `H¹(Γ, C_E)`: restriction to the trivial
  -- subgroup vanishes.
  have htop : ∀ x : groupCohomology M 1, Nat.card (E ≃ₐ[F] E) • x = 0 := by
    intro x
    haveI : Subsingleton ↥(⊥ : Subgroup (E ≃ₐ[F] E)) := inferInstance
    haveI hbot : Subsingleton (groupCohomology
        (Rep.res (⊥ : Subgroup (E ≃ₐ[F] E)).subtype M) 1) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (isZero_groupCohomology_succ_of_subsingleton
          (Rep.res (⊥ : Subgroup (E ≃ₐ[F] E)).subtype M) 0)
    have hh := hcor_res (⊥ : Subgroup (E ≃ₐ[F] E)) x hbot
    rwa [Subgroup.index_bot] at hh
  -- (ii) for every prime `q` dividing the order of `Γ`, the index of a Sylow `q`-subgroup
  -- annihilates `H¹(Γ, C_E)`.
  have hprime : ∀ (q : ℕ), Nat.Prime q → q ∣ Nat.card (E ≃ₐ[F] E) →
      ∀ x : groupCohomology M 1, ∃ n : ℕ, ¬ q ∣ n ∧ n • x = 0 := by
    intro q hq _ x
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨Q⟩ : Nonempty (Sylow q (E ≃ₐ[F] E)) := Sylow.nonempty
    exact ⟨Q.index, Sylow.not_dvd_index Q,
      hcor_res (Q : Subgroup (E ≃ₐ[F] E)) x
        (subsingleton_groupCohomology_one_res_ideleClassGroup_of_isPGroup h q hq
          (Q : Subgroup (E ≃ₐ[F] E)) Q.isPGroup')⟩
  -- (iii) hence every element of `H¹(Γ, C_E)` is zero.
  intro x
  have hx : addOrderOf x = 1 := by
    by_contra hne
    obtain ⟨q, hqprime, hqdiv⟩ := Nat.exists_prime_and_dvd hne
    have hqcard : q ∣ Nat.card (E ≃ₐ[F] E) :=
      dvd_trans hqdiv (addOrderOf_dvd_iff_nsmul_eq_zero.mpr (htop x))
    obtain ⟨n, hnq, hn⟩ := hprime q hqprime hqcard x
    exact hnq (dvd_trans hqdiv (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hn))
  have h1 : (1 : ℕ) • x = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp (by rw [hx])
  simpa using h1

end NK.HassePrinciple
