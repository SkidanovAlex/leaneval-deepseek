import Mathlib
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.IdeleClassGroup
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable
import Submission.NK.GlobalCFT.Inclusion.globalCFT_invariants_ideleClassGroup
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists
import Submission.NK.CFTLib.normClassSubgroup_sup_range_eq_top
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib

open NK.GlobalCFT
open scoped NumberField

/-- **A finite abelian group of order `p ^ 2` with an element whose `p`-th power is not `1` is
cyclic.**  Indeed the order of such an element divides `p ^ 2` but not `p`, hence is `p ^ 2`. -/
theorem isCyclic_of_card_eq_prime_sq_of_pow_ne_one {A : Type*} [CommGroup A] [Finite A]
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card A = p ^ 2) (h : ∃ a : A, a ^ p ≠ 1) :
    IsCyclic A := by
  obtain ⟨a, ha⟩ := h
  have hdvd : orderOf a ∣ p ^ 2 := by
    rw [← hcard]; exact orderOf_dvd_natCard a
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  have hk2 : k = 2 := by
    rcases Nat.lt_or_ge k 2 with hlt | hge
    · exfalso
      have hdiv : orderOf a ∣ p := by
        rw [hk]
        simpa using pow_dvd_pow p (by omega : k ≤ 1)
      exact ha (orderOf_dvd_iff_pow_eq_one.mp hdiv)
    · omega
  refine isCyclic_of_orderOf_eq_card a ?_
  rw [hk, hk2, hcard]

theorem isCyclic_normClassQuotient_prime_sq
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (h : ∃ p : ℕ, p.Prime ∧ Nat.card (L ≃ₐ[K] L) = p ^ 2) :
    IsCyclic (NK.GlobalCFT.IdeleClassGroup K ⧸
      NK.GlobalCFT.Idele.normClassSubgroup K L) := by
  obtain ⟨p, hp, hcard⟩ := h
  haveI : Fact p.Prime := ⟨hp⟩
  -- ### The intermediate field of the cyclic extension
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have hgord : orderOf g = p ^ 2 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  let S : Subgroup (L ≃ₐ[K] L) := Subgroup.zpowers (g ^ p)
  have hSorder : orderOf (g ^ p) = p := by
    rw [orderOf_pow, hgord, Nat.gcd_eq_right (dvd_pow_self p (by norm_num : 2 ≠ 0)),
      pow_two, Nat.mul_div_cancel_left p hp.pos]
  have hScard : Nat.card S = p := by
    show Nat.card ↥(Subgroup.zpowers (g ^ p)) = p
    rw [Nat.card_zpowers, hSorder]
  let M : IntermediateField K L := IntermediateField.fixedField S
  haveI : S.Normal := Subgroup.normal_of_isMulCommutative S
  haveI : FiniteDimensional K ↥M := inferInstance
  haveI : NumberField ↥M := NumberField.of_module_finite K ↥M
  haveI : IsGalois K ↥M := IsGalois.of_fixedField_normal_subgroup S
  haveI : FiniteDimensional ↥M L := inferInstance
  haveI : IsGalois ↥M L := inferInstance
  have hKL : Module.finrank K L = p ^ 2 := (IsGalois.card_aut_eq_finrank K L).symm.trans hcard
  have hML : Module.finrank ↥M L = p := by
    show Module.finrank ↥(IntermediateField.fixedField S) L = p
    rw [IntermediateField.finrank_fixedField_eq_card S, hScard]
  have hMK : Module.finrank K ↥M = p := by
    have hh := Module.finrank_mul_finrank K ↥M L
    rw [hML, hKL] at hh
    rw [pow_two] at hh
    exact Nat.mul_right_cancel hp.pos hh
  have hcycM : IsCyclic (↥M ≃ₐ[K] ↥M) :=
    (IsGalois.normalAutEquivQuotient (K := K) (L := L) S).isCyclic.mp
      (isCyclic_of_surjective (QuotientGroup.mk' S) (QuotientGroup.mk'_surjective S))
  have hcycML : IsCyclic (L ≃ₐ[↥M] L) :=
    (IntermediateField.subgroupEquivAlgEquiv (F := K) (E := L) S).isCyclic.mp
      (Subgroup.isCyclic_zpowers (g ^ p))
  -- ### Index arithmetic
  have hindexA : (Idele.normClassSubgroup K L).index = p ^ 2 := by
    rw [NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic (K := K) (L := L), hKL]
  have hindexB : (Idele.normClassSubgroup ↥M L).index = p := by
    rw [NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic (K := ↥M) (L := L), hML]
  have hindexM : (Idele.normClassSubgroup K ↥M).index = p := by
    rw [NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic (K := K) (L := ↥M), hMK]
  have hcardA : Nat.card (IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) = p ^ 2 := by
    rw [← Subgroup.index_eq_card (Idele.normClassSubgroup K L), hindexA]
  have hcardB : Nat.card (IdeleClassGroup ↥M ⧸ Idele.normClassSubgroup ↥M L) = p := by
    rw [← Subgroup.index_eq_card (Idele.normClassSubgroup ↥M L), hindexB]
  -- ### The canonical inclusion `C_K → C_M` with its two defining properties
  obtain ⟨φ, hφ⟩ := NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists (K := K) (L := ↥M)
    (fun w => Classical.choose (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := ↥M) w))
    (fun w => Classical.choose_spec (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := ↥M) w))
  obtain ⟨ψ, hψ⟩ := NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists
    (K := K) (L := ↥M) _ _ φ hφ
  have hψinv : ∀ q : IdeleClassGroup ↥M,
      (∀ σ : ↥M ≃ₐ[K] ↥M, σ • q = q) ↔ q ∈ ψ.range :=
    fun q => NK.GlobalCFT.Inclusion.globalCFT_invariants_ideleClassGroup _ _ φ hφ ψ hψ q
  have hψinj : Function.Injective ψ :=
    NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective _ _ φ hφ ψ hψ
  have hprod : ∀ q : IdeleClassGroup ↥M,
      ψ (IdeleClassGroup.normClassHom K ↥M q) = ∏ σ : ↥M ≃ₐ[K] ↥M, σ • q :=
    fun q => NK.GlobalCFT.globalCFT_normClassHom_eq_prod_smul _ _ φ hφ ψ hψ q
  -- ### The three norm class quotients
  let NL : Subgroup (IdeleClassGroup K) := Idele.normClassSubgroup K L
  let NM : Subgroup (IdeleClassGroup K) := Idele.normClassSubgroup K ↥M
  let NLM : Subgroup (IdeleClassGroup ↥M) := Idele.normClassSubgroup ↥M L
  -- ### The surjection `Ψ : C_K →* C_M ⧸ N_{L/M}C_L`
  let Ψ : IdeleClassGroup K →* (IdeleClassGroup ↥M ⧸ NLM) := (QuotientGroup.mk' NLM).comp ψ
  have hkey : ψ.range ⊔ NLM = ⊤ :=
    NK.CFTLib.normClassSubgroup_sup_range_eq_top (K := K) (L := L) (M := ↥M)
      p hp hcard hMK ψ hψinv
  have hΨsurj : Function.Surjective Ψ := by
    rintro q
    obtain ⟨q', rfl⟩ := QuotientGroup.mk'_surjective NLM q
    obtain ⟨a, ha, b, hb, hab⟩ :=
      Subgroup.mem_sup.mp (by rw [hkey]; exact Subgroup.mem_top q')
    obtain ⟨x, rfl⟩ := ha
    refine ⟨x, ?_⟩
    change QuotientGroup.mk' NLM (ψ x) = QuotientGroup.mk' NLM q'
    rw [← hab, map_mul]
    have hb1 : QuotientGroup.mk' NLM b = 1 :=
      MonoidHom.mem_ker.mp (by rw [QuotientGroup.ker_mk']; exact hb)
    rw [hb1, mul_one]
  -- ### The norm-induced map `Nbar : B →* A`
  have hNLleNM : NL ≤ NM := by
    intro x hx
    obtain ⟨z, rfl⟩ := Idele.mem_normClassSubgroup.mp hx
    exact Idele.mem_normClassSubgroup.mpr
      ⟨IdeleClassGroup.normClassHom ↥M L z,
        NK.GlobalCFT.NormGroup.globalCFT_normClassHom_trans z⟩
  have hNMne : NM ≠ NL := by
    intro heq
    have h : NM.index = NL.index := by rw [heq]
    rw [hindexM, hindexA] at h
    have hp2 : p < p ^ 2 := by nlinarith [hp.two_le]
    omega
  have hNLMnormal : NLM.Normal := Subgroup.normal_of_isMulCommutative NLM
  have hNLnormal : NL.Normal := Subgroup.normal_of_isMulCommutative NL
  have hker : NLM ≤ ((QuotientGroup.mk' NL).comp (IdeleClassGroup.normClassHom K ↥M)).ker := by
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    obtain ⟨z, rfl⟩ := Idele.mem_normClassSubgroup.mp hy
    rw [NK.GlobalCFT.NormGroup.globalCFT_normClassHom_trans (K := K) (L := ↥M) (M := L) z]
    have hmem : IdeleClassGroup.normClassHom K L z ∈ NL := by
      rw [show NL = (IdeleClassGroup.normClassHom K L).range from
        Idele.normClassSubgroup_eq_range (K := K) (L := L)]
      exact MonoidHom.mem_range.mpr ⟨z, rfl⟩
    exact MonoidHom.mem_ker.mp (by rw [QuotientGroup.ker_mk']; exact hmem)
  let Nbar : (IdeleClassGroup ↥M ⧸ NLM) →* (IdeleClassGroup K ⧸ NL) :=
    QuotientGroup.lift NLM ((QuotientGroup.mk' NL).comp (IdeleClassGroup.normClassHom K ↥M)) hker
  -- ### The key identity: `N_{M/K}(ψ x) = x ^ p`
  have hnrm : ∀ x : IdeleClassGroup K, IdeleClassGroup.normClassHom K ↥M (ψ x) = x ^ p := by
    intro x
    apply hψinj
    rw [hprod (ψ x), map_pow]
    rw [Finset.prod_congr rfl (fun σ _ => (hψinv (ψ x)).mpr ⟨x, rfl⟩ σ)]
    rw [Finset.prod_const, Finset.card_univ]
    congr 1
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank K ↥M, hMK]
  have hNbar_apply : ∀ x : IdeleClassGroup K,
      Nbar (Ψ x) = QuotientGroup.mk' NL (x ^ p) := by
    intro x
    change QuotientGroup.lift NLM
      ((QuotientGroup.mk' NL).comp (IdeleClassGroup.normClassHom K ↥M)) hker
        (ψ x : IdeleClassGroup ↥M ⧸ NLM) = QuotientGroup.mk' NL (x ^ p)
    rw [QuotientGroup.lift_mk']
    change QuotientGroup.mk' NL (IdeleClassGroup.normClassHom K ↥M (ψ x)) = _
    rw [hnrm x]
  -- ### An element of `NM ⧸ NL` that is nontrivial
  obtain ⟨y, hyNM, hyNL⟩ :=
    SetLike.exists_of_lt (lt_of_le_of_ne hNLleNM (Ne.symm hNMne))
  obtain ⟨z, hz⟩ := Idele.mem_normClassSubgroup.mp hyNM
  have hyNbar : Nbar (QuotientGroup.mk' NLM z) ≠ 1 := by
    change QuotientGroup.lift NLM
      ((QuotientGroup.mk' NL).comp (IdeleClassGroup.normClassHom K ↥M)) hker
        (z : IdeleClassGroup ↥M ⧸ NLM) ≠ 1
    rw [QuotientGroup.lift_mk']
    change QuotientGroup.mk' NL (IdeleClassGroup.normClassHom K ↥M z) ≠ 1
    rw [hz]
    intro h1
    exact hyNL (by
      have h1' : (y : IdeleClassGroup K ⧸ Idele.normClassSubgroup K L) = 1 := h1
      exact (QuotientGroup.eq_one_iff y).mp h1')
  obtain ⟨x, hx⟩ := hΨsurj (QuotientGroup.mk' NLM z)
  have hne : QuotientGroup.mk' NL (x ^ p) ≠ 1 := by
    rw [← hNbar_apply x, hx]
    exact hyNbar
  haveI hfin : NL.FiniteIndex :=
    Subgroup.finiteIndex_iff.mpr (by rw [hindexA]; exact pow_ne_zero 2 hp.ne_zero)
  refine isCyclic_of_card_eq_prime_sq_of_pow_ne_one hp hcardA
    ⟨QuotientGroup.mk' NL x, fun hpow => hne (by rw [map_pow]; exact hpow)⟩

end NK.CFTLib
