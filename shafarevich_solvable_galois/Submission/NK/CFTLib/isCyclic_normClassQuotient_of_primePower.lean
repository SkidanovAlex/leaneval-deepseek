import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.CFTLib.isCyclic_normClassQuotient_of_three_le
import Submission.NK.CFTLib.isCyclic_normClassQuotient_prime_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField

namespace NK.CFTLib

open NK.GlobalCFT
open NK.GlobalCFTdeep

/-- Lifting a homomorphism `f` which kills `N` to the quotient `G ⧸ N` does not change its
range. -/
lemma range_lift_eq {G M : Type*} [Group G] [Group M] (N : Subgroup G) [N.Normal]
    (f : G →* M) (hf : N ≤ f.ker) :
    (QuotientGroup.lift N f hf).range = f.range := by
  ext y
  rw [MonoidHom.mem_range, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    exact ⟨x, (QuotientGroup.lift_mk' N hf x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨QuotientGroup.mk' N x, QuotientGroup.lift_mk' N hf x⟩

/-- **Cyclicity of the image of a norm class subgroup.**  For `K ⊆ M ⊆ L` of number fields, the
norm map `N_{M/K} : C_M → C_K` descends to a surjection
`C_M ⧸ N_{L/M}C_L ↠ (N_{M/K}C_M) ⧸ N_{L/K}C_L`; hence the image of `N_{M/K}C_M` in
`C_K ⧸ N_{L/K}C_L` is cyclic whenever `C_M ⧸ N_{L/M}C_L` is. -/
lemma isCyclic_map_normClassSubgroup
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (M : IntermediateField K L) [FiniteDimensional K M] [NumberField ↥M]
    [FiniteDimensional ↥M L] [IsGalois ↥M L]
    (h : IsCyclic (IdeleClassGroup ↥M ⧸ Idele.normClassSubgroup ↥M L)) :
    IsCyclic ↥((Idele.normClassSubgroup K ↥M).map
      (QuotientGroup.mk' (Idele.normClassSubgroup K L))) := by
  let NL : Subgroup (IdeleClassGroup K) := Idele.normClassSubgroup K L
  let NLM : Subgroup (IdeleClassGroup ↥M) := Idele.normClassSubgroup ↥M L
  have hle : NL ≤ Idele.normClassSubgroup K ↥M := Idele.normClassSubgroup_le_of_tower
  let f : IdeleClassGroup ↥M →* (IdeleClassGroup K ⧸ NL) :=
    (QuotientGroup.mk' NL).comp (IdeleClassGroup.normClassHom K ↥M)
  have hfker : NLM ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    obtain ⟨y, rfl⟩ := Idele.mem_normClassSubgroup.mp hx
    show QuotientGroup.mk' NL ((IdeleClassGroup.normClassHom K ↥M)
      ((IdeleClassGroup.normClassHom ↥M L) y)) = 1
    rw [NormGroup.globalCFT_normClassHom_trans y]
    exact (QuotientGroup.eq_one_iff _).mpr (Idele.mem_normClassSubgroup.mpr ⟨y, rfl⟩)
  let φ : (IdeleClassGroup ↥M ⧸ NLM) →* (IdeleClassGroup K ⧸ NL) :=
    QuotientGroup.lift NLM f hfker
  have hfrange : f.range = (Idele.normClassSubgroup K ↥M).map (QuotientGroup.mk' NL) := by
    rw [MonoidHom.range_comp, ← Idele.normClassSubgroup_eq_range]
  have hφrange : φ.range = (Idele.normClassSubgroup K ↥M).map (QuotientGroup.mk' NL) := by
    rw [range_lift_eq NLM f hfker, hfrange]
  rw [← hφrange]
  exact isCyclic_of_surjective φ.rangeRestrict (MonoidHom.rangeRestrict_surjective φ)

/-- **Strong induction on the order of the Galois group.** -/
private theorem aux : ∀ n : ℕ, ∀ {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic (L ≃ₐ[K] L)],
    Nat.card (L ≃ₐ[K] L) = n →
    (∃ p a : ℕ, p.Prime ∧ 0 < a ∧ Nat.card (L ≃ₐ[K] L) = p ^ a) →
    IsCyclic (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K L _ _ _ _ _ _ _ _ hcard h
    obtain ⟨p, a, hp, ha, hcardpa⟩ := h
    haveI : Fact p.Prime := ⟨hp⟩
    rcases lt_or_ge a 3 with ha_lt | ha3
    · interval_cases a
      · -- `a = 1`
        have hindex : (Idele.normClassSubgroup K L).index = p := by
          rw [index_eq_finrank_of_isCyclic, ← IsGalois.card_aut_eq_finrank K L, hcardpa, pow_one]
        have hcardA : Nat.card (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) = p := by
          rw [← Subgroup.index_eq_card]; exact hindex
        exact isCyclic_of_prime_card hcardA
      · -- `a = 2`
        exact isCyclic_normClassQuotient_prime_sq (K := K) (L := L) ⟨p, hp, hcardpa⟩
    · -- `a ≥ 3`
      obtain ⟨σ, hσgen⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
      have hσord : orderOf σ = p ^ a := by
        rw [orderOf_eq_card_of_forall_mem_zpowers hσgen, hcardpa]
      have hpoweq : p ^ a = p ^ (a - 1) * p := by
        have h1 : (a - 1) + 1 = a := Nat.sub_add_cancel (by omega : 1 ≤ a)
        calc p ^ a = p ^ ((a - 1) + 1) := by rw [h1]
          _ = p ^ (a - 1) * p := pow_succ _ _
      have hpoweq2 : p ^ a = p * p ^ (a - 1) := by
        have h2 : 1 + (a - 1) = a := by omega
        calc p ^ a = p ^ (1 + (a - 1)) := by rw [h2]
          _ = p * p ^ (a - 1) := by rw [pow_add, pow_one]
      set S1 : Subgroup (L ≃ₐ[K] L) := Subgroup.zpowers (σ ^ p) with hS1def
      set S2 : Subgroup (L ≃ₐ[K] L) := Subgroup.zpowers (σ ^ (p ^ (a - 1))) with hS2def
      have hdiv1 : p ^ a / p = p ^ (a - 1) := by
        have h3 := Nat.pow_div (x := p) (n := 1) (m := a) (by omega : 1 ≤ a) hp.pos
        rwa [pow_one] at h3
      have hS1card : Nat.card ↥S1 = p ^ (a - 1) := by
        rw [hS1def, Nat.card_zpowers, orderOf_pow, hσord,
          Nat.gcd_eq_right (dvd_pow_self p (by omega : a ≠ 0)), hdiv1]
      have hdiv2 : p ^ a / p ^ (a - 1) = p := by
        have h4 := Nat.pow_div (x := p) (n := a - 1) (m := a) (by omega : a - 1 ≤ a) hp.pos
        rw [show a - (a - 1) = 1 from by omega, pow_one] at h4
        exact h4
      have hS2card : Nat.card ↥S2 = p := by
        rw [hS2def, Nat.card_zpowers, orderOf_pow, hσord,
          Nat.gcd_eq_right (pow_dvd_pow p (by omega : a - 1 ≤ a)), hdiv2]
      have hS21 : S2 ≤ S1 := by
        rw [hS2def, hS1def]
        refine Subgroup.zpowers_le.mpr ?_
        have h5 : p ^ (a - 1) = p * p ^ (a - 2) := by
          rw [show a - 1 = a - 2 + 1 from by omega, pow_succ']
        rw [h5, pow_mul]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
      haveI hS1normal : S1.Normal := Subgroup.normal_of_isMulCommutative S1
      haveI hS2normal : S2.Normal := Subgroup.normal_of_isMulCommutative S2
      set M1 : IntermediateField K L := IntermediateField.fixedField S1 with hM1def
      set M2 : IntermediateField K L := IntermediateField.fixedField S2 with hM2def
      haveI : FiniteDimensional K ↥M1 := inferInstance
      haveI : NumberField ↥M1 := NumberField.of_module_finite K ↥M1
      haveI : FiniteDimensional K ↥M2 := inferInstance
      haveI : NumberField ↥M2 := NumberField.of_module_finite K ↥M2
      haveI : IsGalois K ↥M1 := IsGalois.of_fixedField_normal_subgroup S1
      haveI : IsGalois K ↥M2 := IsGalois.of_fixedField_normal_subgroup S2
      have hKL : Module.finrank K L = p ^ a := (IsGalois.card_aut_eq_finrank K L).symm.trans hcardpa
      have hM1L : Module.finrank ↥M1 L = p ^ (a - 1) := by
        rw [hM1def, IntermediateField.finrank_fixedField_eq_card, hS1card]
      have hM2L : Module.finrank ↥M2 L = p := by
        rw [hM2def, IntermediateField.finrank_fixedField_eq_card, hS2card]
      have hM1K : Module.finrank K ↥M1 = p := by
        have h := Module.finrank_mul_finrank K ↥M1 L
        rw [hM1L, hKL, hpoweq2] at h
        exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) h
      have hM2K : Module.finrank K ↥M2 = p ^ (a - 1) := by
        have h := Module.finrank_mul_finrank K ↥M2 L
        rw [hM2L, hKL, hpoweq] at h
        exact Nat.eq_of_mul_eq_mul_right hp.pos h
      -- instances for the two smaller extensions
      haveI hcycM1L : IsCyclic (L ≃ₐ[↥M1] L) :=
        (IntermediateField.subgroupEquivAlgEquiv (F := K) (E := L) S1).isCyclic.mp
          (Subgroup.isCyclic_zpowers (σ ^ p))
      haveI hcycKM1 : IsCyclic (↥M1 ≃ₐ[K] ↥M1) :=
        (IsGalois.normalAutEquivQuotient (K := K) (L := L) S1).isCyclic.mp
          (isCyclic_of_surjective (QuotientGroup.mk' S1) (QuotientGroup.mk'_surjective S1))
      haveI hcycKM2 : IsCyclic (↥M2 ≃ₐ[K] ↥M2) :=
        (IsGalois.normalAutEquivQuotient (K := K) (L := L) S2).isCyclic.mp
          (isCyclic_of_surjective (QuotientGroup.mk' S2) (QuotientGroup.mk'_surjective S2))
      have hcardM1L : Nat.card (L ≃ₐ[↥M1] L) = p ^ (a - 1) :=
        (IsGalois.card_aut_eq_finrank ↥M1 L).trans hM1L
      have hcardKM2 : Nat.card (↥M2 ≃ₐ[K] ↥M2) = p ^ (a - 1) :=
        (IsGalois.card_aut_eq_finrank K ↥M2).trans hM2K
      have hn : n = p ^ a := hcard.symm.trans hcardpa
      have hlt : p ^ (a - 1) < n := by
        rw [hn]
        exact Nat.pow_lt_pow_right hp.one_lt (by omega : a - 1 < a)
      have hcycl1 : IsCyclic (IdeleClassGroup ↥M1 ⧸ Idele.normClassSubgroup ↥M1 L) :=
        ih (p ^ (a - 1)) hlt hcardM1L ⟨p, a - 1, hp, by omega, hcardM1L⟩
      have hcycl2 : IsCyclic (IdeleClassGroup K ⧸ Idele.normClassSubgroup K ↥M2) :=
        ih (p ^ (a - 1)) hlt hcardKM2 ⟨p, a - 1, hp, by omega, hcardKM2⟩
      have hidx1 : (Idele.normClassSubgroup K ↥M1).index = p := by
        rw [index_eq_finrank_of_isCyclic, hM1K]
      have hidx2 : (Idele.normClassSubgroup K ↥M2).index = p ^ (a - 1) := by
        rw [index_eq_finrank_of_isCyclic, hM2K]
      have hM12 : M1 ≤ M2 := by
        rw [hM1def, hM2def]
        exact IntermediateField.fixedField_le hS21
      exact isCyclic_normClassQuotient_of_three_le (K := K) (L := L) hp ha3 hcardpa
        M1 M2 hM12 hidx1 hidx2 hcycl1 hcycl2

theorem isCyclic_normClassQuotient_of_primePower
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (h : ∃ p a : ℕ, p.Prime ∧ 0 < a ∧ Nat.card (L ≃ₐ[K] L) = p ^ a) :
    IsCyclic (NK.GlobalCFT.IdeleClassGroup K ⧸
      NK.GlobalCFT.Idele.normClassSubgroup K L) :=
  aux _ rfl h

end NK.CFTLib
