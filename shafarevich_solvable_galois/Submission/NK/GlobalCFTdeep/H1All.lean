import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Torsor.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFTdeep.H1Cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H¹(Gal(L/K), C_L) = 0` for every finite Galois extension, unconditionally

This file proves Milne's *Class Field Theory*, Theorem 5.1(b) —

  `H¹(Gal(L/K), C_L) = 0` for every finite Galois extension of number fields,

and its form for every subgroup `H ≤ Gal(L/K)` — with **no input at all**.  The proof is the
classical one and uses the unconditional results of this chapter:

* the **cyclic case** (`NK.GlobalCFTdeep.subsingleton_groupCohomology_one_of_isCyclic`, from the
  Kummer-theoretic second inequality for cyclic extensions of prime degree and the
  Herbrand-quotient computation), and
* the **`p`-group case** by strong induction on the order of the group: for `N ◁ Γ` of index `p`
  and `M = E^N`, the inflation–restriction sequence in degree one
  `H¹(Γ/N, C_E^N) → H¹(Γ, C_E) → H¹(N, C_E)`
  has vanishing ends (the quotient is cyclic of prime order — the cyclic case — and the right end is
  the induction hypothesis at `E / M`); and
* the **general case** by restriction to Sylow subgroups: `cores ∘ res = [Γ : S]` in degree one
  (`NU.cor_resNatTrans_comp_apply`), so an element killed by restriction to a Sylow `ℓ`-subgroup is
  annihilated by `[Γ : S_ℓ]`, and varying `ℓ` over the primes dividing its order forces it to be
  zero.

## Main results

* `NK.GlobalCFTdeep.subsingleton_groupCohomology_one_ideleClassGroup_of_isPGroup`;
* `NK.GlobalCFTdeep.subsingleton_groupCohomology_one_ideleClassGroup` (all `L/K` Galois);
* `NK.GlobalCFTdeep.subsingleton_groupCohomology_one_res_ideleClassGroup` (all subgroups `H`) —
  this is the `h1` field of `NK.GlobalCFT.CohomologicalFieldAxiom`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFTdeep

open NK.GlobalCFT

/-- **`H¹(Gal(E/F), C_E) = 0` for a `p`-group level**, unconditionally.  Strong induction on
`Nat.card (E ≃ₐ[F] E)`: for `N ◁ Γ` with `Γ ⧸ N` of order `p` and `M = E^N`, the
inflation–restriction sequence in degree one has vanishing ends. -/
theorem subsingleton_groupCohomology_one_ideleClassGroup_of_isPGroup {p : ℕ} [Fact p.Prime]
    {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] (hG : IsPGroup p (E ≃ₐ[F] E)) :
    Subsingleton (groupCohomology (IdeleClassGroup.rep F E) 1) := by
  have key : ∀ n, ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
      [Algebra F E] [FiniteDimensional F E] [IsGalois F E],
      Nat.card (E ≃ₐ[F] E) = n → IsPGroup p (E ≃ₐ[F] E) →
      Subsingleton (groupCohomology (IdeleClassGroup.rep F E) 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro F E _ _ _ _ _ _ _ hcard hG
      rcases Nat.lt_or_ge 1 n with h1 | h1
      · -- nontrivial
        haveI hnt : Nontrivial (E ≃ₐ[F] E) := by
          rw [← not_subsingleton_iff_nontrivial]
          intro hsub
          rw [Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩] at hcard
          omega
        obtain ⟨N, hNnorm, hNindex⟩ := NK.HassePrinciple.exists_normal_subgroup_index_eq_prime hG hnt
        haveI := hNnorm
        have hNlt : Nat.card ↥N < n := by
          have hmul : Nat.card ↥N * N.index = Nat.card (E ≃ₐ[F] E) := N.card_mul_index
          rw [hNindex, hcard] at hmul
          have hlt : Nat.card ↥N < Nat.card ↥N * p := by
            calc Nat.card ↥N = Nat.card ↥N * 1 := (mul_one _).symm
              _ < Nat.card ↥N * p := Nat.mul_lt_mul_of_pos_left (Fact.out : p.Prime).one_lt Nat.card_pos
          rw [hmul] at hlt
          exact hlt
        set M : IntermediateField F E := IntermediateField.fixedField N with hM
        have hMcard : Nat.card (E ≃ₐ[↥M] E) = Nat.card ↥N :=
          (Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv N).toEquiv).symm
        have hMN : Subsingleton (groupCohomology (IdeleClassGroup.rep ↥M E) 1) :=
          ih (Nat.card ↥N) hNlt hMcard
            ((hG.to_subgroup N).of_equiv (IntermediateField.subgroupEquivAlgEquiv N))
        have h1' : Subsingleton (groupCohomology (Rep.res N.subtype (IdeleClassGroup.rep F E)) 1) := by
          haveI : Subsingleton (groupCohomology (IdeleClassGroup.rep ↥M E) 1) := hMN
          exact ((groupCohomology.mapIso (G := ↥N) (H := (E ≃ₐ[↥M] E))
            (A := IdeleClassGroup.rep ↥M E)
            (B := Rep.res N.subtype (IdeleClassGroup.rep F E))
            (IntermediateField.subgroupEquivAlgEquiv N) (LinearEquiv.refl ℤ _)
            (by intro g; rfl) 1).toLinearEquiv).injective.subsingleton
        -- the quotient side, from the cyclic case for `M / F`
        haveI : IsGalois F ↥M := IsGalois.of_fixedField_normal_subgroup N
        have hQcard : Nat.card ((E ≃ₐ[F] E) ⧸ N) = p := by
          rw [← Subgroup.index_eq_card]; exact hNindex
        have hcyc : IsCyclic (↥M ≃ₐ[F] ↥M) := by
          have h2 : Nat.card (↥M ≃ₐ[F] ↥M) = p := by
            rw [← Nat.card_congr (IsGalois.normalAutEquivQuotient N).toEquiv, hQcard]
          exact isCyclic_of_prime_card h2
        have hMq : Subsingleton (groupCohomology (IdeleClassGroup.rep F ↥M) 1) :=
          subsingleton_groupCohomology_one_of_isCyclic (K := F) (L := ↥M)
        obtain ⟨hiso⟩ := NK.HassePrinciple.repIso_quotientToInvariants_fixedField (K := F) (L := E) N
        have hB : Subsingleton (groupCohomology
            (Rep.res (IsGalois.normalAutEquivQuotient N).toMonoidHom
              (IdeleClassGroup.rep F ↥M)) 1) := by
          haveI : Subsingleton (groupCohomology (IdeleClassGroup.rep F ↥M) 1) := hMq
          exact ((groupCohomology.mapIso
            (G := (E ≃ₐ[F] E) ⧸ N) (H := (↥M ≃ₐ[F] ↥M))
            (A := IdeleClassGroup.rep F ↥M)
            (B := Rep.res (IsGalois.normalAutEquivQuotient N).toMonoidHom
              (IdeleClassGroup.rep F ↥M))
            (IsGalois.normalAutEquivQuotient N) (LinearEquiv.refl ℤ _)
            (by intro g; rfl) 1).toLinearEquiv).injective.subsingleton
        have h2' : Subsingleton
            (groupCohomology ((IdeleClassGroup.rep F E).quotientToInvariants N) 1) := by
          refine @Function.Injective.subsingleton _ _ _
            (((groupCohomology.functor ℤ ((E ≃ₐ[F] E) ⧸ N) 1).mapIso hiso).toLinearEquiv).injective ?_
          exact hB
        exact NK.HassePrinciple.subsingleton_groupCohomology_one_of_ends (IdeleClassGroup.rep F E) N h1' h2'
      · -- trivial
        have hle : n ≤ 1 := by omega
        have hle' : Nat.card (E ≃ₐ[F] E) ≤ 1 := by rw [hcard]; exact hle
        have hcard1 : Nat.card (E ≃ₐ[F] E) = 1 := le_antisymm hle' Nat.card_pos
        haveI : Subsingleton (E ≃ₐ[F] E) := (Nat.card_eq_one_iff_unique.mp hcard1).1
        have h : CategoryTheory.Limits.IsZero
            (groupCohomology (IdeleClassGroup.rep F E) (0+1)) :=
          isZero_groupCohomology_succ_of_subsingleton _ 0
        exact ModuleCat.isZero_iff_subsingleton.mp h
  exact key (Nat.card (E ≃ₐ[F] E)) rfl hG

/-- **`H¹(H, C_E) = 0` for a `q`-subgroup `H ≤ Gal(E/F)`**, from the `q`-group case applied to
the extension `E / E^H` (whose Galois group is `H`). -/
theorem subsingleton_groupCohomology_one_res_ideleClassGroup_of_isPGroup {F E : Type} [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    [IsGalois F E] {q : ℕ} [Fact q.Prime] (H : Subgroup (E ≃ₐ[F] E)) (hH : IsPGroup q H) :
    Subsingleton (groupCohomology (Rep.res H.subtype (IdeleClassGroup.rep F E)) 1) := by
  classical
  let K' : IntermediateField F E := IntermediateField.fixedField H
  haveI : NumberField ↥K' := inferInstance
  haveI : FiniteDimensional ↥K' E := inferInstance
  haveI : IsGalois ↥K' E := inferInstance
  have hpg : IsPGroup q (E ≃ₐ[↥K'] E) :=
    IsPGroup.of_equiv hH (IntermediateField.subgroupEquivAlgEquiv H)
  have hK : Subsingleton (groupCohomology (IdeleClassGroup.rep ↥K' E) 1) :=
    subsingleton_groupCohomology_one_ideleClassGroup_of_isPGroup (p := q) hpg
  haveI : Subsingleton (groupCohomology (IdeleClassGroup.rep ↥K' E) 1) := hK
  exact ((groupCohomology.mapIso (G := ↥H) (H := (E ≃ₐ[↥K'] E))
      (A := IdeleClassGroup.rep ↥K' E)
      (B := Rep.res H.subtype (IdeleClassGroup.rep F E))
      (IntermediateField.subgroupEquivAlgEquiv H) (LinearEquiv.refl ℤ _)
      (by intro g; rfl) 1).toLinearEquiv).injective.subsingleton

/-- **`H¹(Γ, C_E) = 0` for every finite Galois extension of number fields.**  Reduction to Sylow
subgroups: `cores ∘ res = [Γ : S]` in degree one, so an element killed by restriction to a Sylow
`ℓ`-subgroup has order dividing `[Γ : S_ℓ]`, and varying `ℓ` forces it to vanish. -/
theorem subsingleton_groupCohomology_one_ideleClassGroup {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] :
    Subsingleton (groupCohomology (IdeleClassGroup.rep F E) 1) := by
  classical
  set M : Rep.{0,0,0} ℤ (E ≃ₐ[F] E) := IdeleClassGroup.rep F E with hM
  suffices hmain : ∀ x : groupCohomology M 1, x = 0 from
    ⟨fun x y => by rw [hmain x, hmain y]⟩
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
  have hprime : ∀ (q : ℕ), Nat.Prime q → q ∣ Nat.card (E ≃ₐ[F] E) →
      ∀ x : groupCohomology M 1, ∃ n : ℕ, ¬ q ∣ n ∧ n • x = 0 := by
    intro q hq _ x
    haveI : Fact q.Prime := ⟨hq⟩
    obtain ⟨Q⟩ : Nonempty (Sylow q (E ≃ₐ[F] E)) := Sylow.nonempty
    exact ⟨Q.index, Sylow.not_dvd_index Q,
      hcor_res (Q : Subgroup (E ≃ₐ[F] E)) x
        (subsingleton_groupCohomology_one_res_ideleClassGroup_of_isPGroup
          (F := F) (E := E) (q := q) (Q : Subgroup (E ≃ₐ[F] E)) Q.isPGroup')⟩
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

/-- **`H¹(H, C_L) = 0` for every subgroup `H ≤ Gal(L/K)`**: apply the previous result to the
Galois extension `L / L^H` (whose Galois group is `H`) and transport along the equivariant
identification `Gal(L/L^H) ≅ H`.  This is the `h1` field of
`NK.GlobalCFT.CohomologicalFieldAxiom`. -/
theorem subsingleton_groupCohomology_one_res_ideleClassGroup {K L : Type} [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (H : Subgroup (L ≃ₐ[K] L)) :
    Subsingleton (groupCohomology (Rep.res H.subtype (IdeleClassGroup.rep K L)) 1) := by
  classical
  let K' : IntermediateField K L := IntermediateField.fixedField H
  haveI : NumberField ↥K' := inferInstance
  haveI : FiniteDimensional ↥K' L := inferInstance
  haveI : IsGalois ↥K' L := inferInstance
  have hK' : Subsingleton (groupCohomology (IdeleClassGroup.rep ↥K' L) 1) :=
    subsingleton_groupCohomology_one_ideleClassGroup
  haveI : Subsingleton (groupCohomology (IdeleClassGroup.rep ↥K' L) 1) := hK'
  exact ((groupCohomology.mapIso (G := ↥H) (H := (L ≃ₐ[↥K'] L))
      (A := IdeleClassGroup.rep ↥K' L)
      (B := Rep.res H.subtype (IdeleClassGroup.rep K L))
      (IntermediateField.subgroupEquivAlgEquiv H) (LinearEquiv.refl ℤ _)
      (by intro g; rfl) 1).toLinearEquiv).injective.subsingleton

end NK.GlobalCFTdeep
