import Mathlib
import Submission.NK.CFTLib.ARL.AuxField
import Submission.NK.CFTLib.ARL.auxField_arith
import Submission.NK.CFTLib.ARL.disjoint_restrictScalars_adjoin_zeta
import Submission.NK.CFTLib.ARL.isGalois_cyclotomicField_over_base
import Submission.NK.CFTLib.ARL.autToPow_eq_of_pow_eq
import Submission.NK.CFTLib.ARL.AuxFieldBase
import Submission.NK.Chebotarev.Basic
import Submission.NK.Chebotarev.IsFrobAtRestrictNormalHom
import Submission.NK.FieldTheory.Galois.exists_prod_restrictNormalHom_of_card
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Artin's auxiliary-field lemma (existence form)

This module proves `NK.CFTLib.ARL.auxField_exists_one`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.CFTLib.ARL

open IntermediateField

theorem auxField_exists_one (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    (m : ℕ) (hm : 0 < m) : NK.CFTLib.ARL.AuxFieldHyp K L m := by
  classical
  intro s hs S hS
  -- ## Part 0: a generator of the Galois group
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  set n : ℕ := Module.finrank K L with hn
  have hnpos : 0 < n := Module.finrank_pos
  have hordg₀ : orderOf g₀ = n := by
    rw [hn, ← IsGalois.card_aut_eq_finrank]
    exact orderOf_eq_card_of_forall_mem_zpowers hg₀
  -- ## Part 1: the arithmetic input
  set a : s → ℕ := fun 𝔭 => Ideal.absNorm (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal with ha
  have ha_gt : ∀ i : s, 1 < a i := by
    intro 𝔭
    haveI : (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal.IsMaximal :=
      Ring.DimensionLEOne.maximalOfPrime (𝔭 : NK.Chebotarev.PrimeIdeal K).ne_bot
        (𝔭 : NK.Chebotarev.PrimeIdeal K).isPrime
    haveI hfin : Finite (𝓞 K ⧸ (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal) :=
      Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum _
    haveI : Fintype (𝓞 K ⧸ (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal) := Fintype.ofFinite _
    haveI : Field (𝓞 K ⧸ (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal) := Ideal.Quotient.field _
    have h : a 𝔭 = Nat.card (𝓞 K ⧸ (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal) := by
      rw [ha]
      simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [h, Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  set Bnd : ℕ := max (max m (max (NumberField.discr K).natAbs (NumberField.discr L).natAbs))
      ((Finset.univ.sup a) + 1) with hBnd
  set T : Finset ℕ := ((Finset.range (Bnd + 1)).filter Nat.Prime) ∪ S with hT
  have hTprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact (Finset.mem_filter.mp h).2
    · exact hS p h
  obtain ⟨M, hMne, ℓ, hℓprime, hM_avoid, hM_cop_a, hℓ_cop_M, hrel⟩ :=
    auxField_arith n hnpos a ha_gt T hTprime
  haveI : NeZero M := hMne
  have hm_Bnd : m ≤ Bnd := by
    rw [hBnd]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hdK_Bnd : (NumberField.discr K).natAbs ≤ Bnd := by
    rw [hBnd]
    refine le_trans (le_max_left _ _) (le_trans (le_max_right m _) (le_max_left _ _))
  have hdL_Bnd : (NumberField.discr L).natAbs ≤ Bnd := by
    rw [hBnd]
    refine le_trans (le_max_right _ _)
      (le_trans (le_max_right m _) (le_max_left _ _))
  have hmemT : ∀ p : ℕ, p.Prime → p ≤ Bnd → p ∈ T := fun p hp hple =>
    Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hple), hp⟩)
  have hM_coprime_m : M.Coprime m := by
    refine Nat.coprime_of_dvd (fun p hp hpdvdM hpdvdm => ?_)
    exact hM_avoid p (hmemT p hp (le_trans (Nat.le_of_dvd hm hpdvdm) hm_Bnd)) hpdvdM
  have hM_avoidS : ∀ p ∈ S, ¬ p ∣ M := fun p hp => hM_avoid p (Finset.mem_union_right _ hp)
  have hM_absNorm : ∀ p : ℕ, p.Prime → p ∣ M → ∀ 𝔭 ∈ s, ¬ p ∣ Ideal.absNorm 𝔭.asIdeal := by
    intro p hp hpdvd 𝔭 h𝔭 hpdvd𝔭
    have hc : Nat.Coprime (a ⟨𝔭, h𝔭⟩) M := hM_cop_a ⟨𝔭, h𝔭⟩
    have h1 : p ∣ a ⟨𝔭, h𝔭⟩ := by
      rw [ha]
      simpa using hpdvd𝔭
    have h2 : p ∣ (a ⟨𝔭, h𝔭⟩).gcd M := Nat.dvd_gcd h1 hpdvd
    rw [hc.gcd_eq_one] at h2
    exact hp.not_dvd_one h2
  have hM_discrL : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr L).natAbs := by
    intro p hp hpdvd hpd
    have hple : p ≤ (NumberField.discr L).natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr (NumberField.discr_ne_zero L)) hpd
    exact hM_avoid p (hmemT p hp (le_trans hple hdL_Bnd)) hpdvd
  have hM_discrK : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr K).natAbs := by
    intro p hp hpdvd hpd
    have hple : p ≤ (NumberField.discr K).natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)) hpd
    exact hM_avoid p (hmemT p hp (le_trans hple hdK_Bnd)) hpdvd
  have hM_not_mem : ∀ 𝔭 ∈ s, (M : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro 𝔭 h𝔭 hmem
    have hge := ha_gt ⟨𝔭, h𝔭⟩
    have hcop : Nat.Coprime (Ideal.absNorm (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal) M := by
      have h := hM_cop_a ⟨𝔭, h𝔭⟩
      rw [ha] at h
      simpa using h
    have hle : Ideal.span {((M : ℕ) : 𝓞 K)} ≤ (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal :=
      Ideal.span_le.mpr (by simpa using hmem)
    have hdvd : Ideal.absNorm (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal ∣ M ^ Module.finrank ℤ (𝓞 K) := by
      have h := Ideal.absNorm_dvd_absNorm_of_le hle
      rw [Ideal.absNorm_span_singleton, Algebra.norm_natCast, Int.natAbs_pow,
        Int.natAbs_natCast] at h
      exact h
    have h2 : Nat.Coprime (Ideal.absNorm (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal)
        (M ^ Module.finrank ℤ (𝓞 K)) := hcop.pow_right _
    have hone : Ideal.absNorm (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal = 1 :=
      Nat.Coprime.eq_one_of_dvd h2 hdvd
    have hge' : 1 < Ideal.absNorm (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal := by
      rw [ha] at hge
      simpa using hge
    omega
  refine ⟨M, hMne, hM_coprime_m, hM_avoidS, hM_absNorm, ?_, ?_⟩
  · exact disjoint_restrictScalars_adjoin_zeta M hM_discrL
  · -- ## Part 2: the auxiliary field
    set Ω := CyclotomicField M L with hΩ
    set ζ := IsCyclotomicExtension.zeta M L Ω with hζdef
    have hζprim : IsPrimitiveRoot ζ M := IsCyclotomicExtension.zeta_spec M L Ω
    set A : IntermediateField K Ω := (⊥ : IntermediateField L Ω).restrictScalars K with hA
    set B : IntermediateField K Ω := IntermediateField.adjoin K ({ζ} : Set Ω) with hB
    haveI hGalΩ : IsGalois K Ω := isGalois_cyclotomicField_over_base (K := K) (L := L) M
    have hAB : A ⊓ B = ⊥ := by
      rw [hA, hB, hζdef]
      exact disjoint_iff.mp (disjoint_restrictScalars_adjoin_zeta M hM_discrL)
    have hsupAB : A ⊔ B = ⊤ := by
      rw [hA, hB, hζdef]
      exact sup_restrictScalars_adjoin_zeta_eq_top_base (K := K) (L := L) M
    have hBcard : Module.finrank K ↥B = M.totient := by
      rw [hB, hζdef]
      exact finrank_adjoin_zeta_eq_totient (K := K) (L := L) M hM_discrK
    haveI hBcyc : IsCyclotomicExtension {M} K ↥B := by
      rw [hB]
      exact (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin M K Ω _
        hζprim).mpr rfl
    haveI hBgal : IsGalois K ↥B := IsCyclotomicExtension.isGalois {M} K ↥B
    have hζBmem : ζ ∈ B := by
      rw [hB]; exact IntermediateField.subset_adjoin K _ (Set.mem_singleton ζ)
    have hζB : IsPrimitiveRoot (⟨ζ, hζBmem⟩ : ↥B) M :=
      hζprim.of_map_of_injective (f := algebraMap ↥B Ω)
        (FaithfulSMul.algebraMap_injective ↥B Ω)
    obtain ⟨τB, hτB⟩ := exists_algEquiv_primitiveRoot_pow (K := K) (B := ↥B) M hBcard hζB
      ((hℓprime.coprime_iff_not_dvd).mpr hℓ_cop_M)
    have hArange : (IsScalarTower.toAlgHom K L Ω).fieldRange = A := by
      rw [hA]
      apply SetLike.ext
      intro x
      rw [AlgHom.mem_fieldRange]
      constructor
      · rintro ⟨y, rfl⟩
        exact (IntermediateField.mem_restrictScalars K).mpr (IntermediateField.mem_bot.mpr ⟨y, rfl⟩)
      · intro hx
        obtain ⟨y, hy⟩ := (IntermediateField.mem_bot).mp
          ((IntermediateField.mem_restrictScalars K).mp hx)
        exact ⟨y, hy⟩
    haveI hAgal : IsGalois K ↥A := by
      rw [← hArange]
      exact IsGalois.of_algEquiv (AlgEquiv.ofInjective (IsScalarTower.toAlgHom K L Ω)
        (FaithfulSMul.algebraMap_injective L Ω))
    haveI hFintypeA : Fintype (↥A ≃ₐ[K] ↥A) := AlgEquiv.fintype K ↥A
    have hfrA : Module.finrank K ↥A = n := by
      rw [hn]
      rw [show Module.finrank K ↥A = Module.finrank K ↥(⊥ : IntermediateField L Ω) from rfl,
        ← Module.finrank_mul_finrank K L ↥(⊥ : IntermediateField L Ω),
        (IntermediateField.botEquiv L Ω).toLinearEquiv.finrank_eq, Module.finrank_self, mul_one]
    let ρ : (Ω ≃ₐ[K] Ω) →* ((↥A ≃ₐ[K] ↥A) × (↥B ≃ₐ[K] ↥B)) :=
      (AlgEquiv.restrictNormalHom A).prod (AlgEquiv.restrictNormalHom B)
    have hkerA : A.fixingSubgroup = (AlgEquiv.restrictNormalHom A).ker := by
      ext σ
      rw [IntermediateField.mem_fixingSubgroup_iff, MonoidHom.mem_ker]
      constructor
      · intro h
        ext x
        rw [AlgEquiv.one_apply, AlgEquiv.restrictNormalHom_apply]
        exact h x x.2
      · intro h x hx
        have h2 := congrArg (fun f : ↥A ≃ₐ[K] ↥A => (f ⟨x, hx⟩ : Ω)) h
        rw [AlgEquiv.restrictNormalHom_apply] at h2
        simpa using h2
    have hkerB : B.fixingSubgroup = (AlgEquiv.restrictNormalHom B).ker := by
      ext σ
      rw [IntermediateField.mem_fixingSubgroup_iff, MonoidHom.mem_ker]
      constructor
      · intro h
        ext x
        rw [AlgEquiv.one_apply, AlgEquiv.restrictNormalHom_apply]
        exact h x x.2
      · intro h x hx
        have h2 := congrArg (fun f : ↥B ≃ₐ[K] ↥B => (f ⟨x, hx⟩ : Ω)) h
        rw [AlgEquiv.restrictNormalHom_apply] at h2
        simpa using h2
    have hρinj : Function.Injective ρ := by
      intro σ τ h
      have h1 : AlgEquiv.restrictNormalHom A σ = AlgEquiv.restrictNormalHom A τ :=
        congrArg Prod.fst h
      have h2 : AlgEquiv.restrictNormalHom B σ = AlgEquiv.restrictNormalHom B τ :=
        congrArg Prod.snd h
      have hmemA : σ⁻¹ * τ ∈ A.fixingSubgroup := by
        rw [hkerA, MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
      have hmemB : σ⁻¹ * τ ∈ B.fixingSubgroup := by
        rw [hkerB, MonoidHom.mem_ker, map_mul, map_inv, h2, inv_mul_cancel]
      have hmem : σ⁻¹ * τ ∈ (A ⊔ B).fixingSubgroup := by
        rw [IntermediateField.fixingSubgroup_sup]
        exact ⟨hmemA, hmemB⟩
      rw [hsupAB, IntermediateField.fixingSubgroup_top] at hmem
      have h3 : σ⁻¹ * τ = 1 := Subgroup.mem_bot.mp hmem
      have h4 : τ = σ := by
        have h5 := congrArg (fun x => σ * x) h3
        simp only [mul_one] at h5
        rw [← mul_assoc, mul_inv_cancel, one_mul] at h5
        exact h5
      exact h4.symm
    have hfrΩsup : Module.finrank K Ω = Module.finrank K ↥(A ⊔ B) := by
      rw [hsupAB]
      exact (LinearEquiv.finrank_eq
        ((IntermediateField.topEquiv (F := K) (E := Ω)).toLinearEquiv)).symm
    haveI hTopGal : IsGalois K ↥(⊤ : IntermediateField K Ω) :=
      IsGalois.of_algEquiv (IntermediateField.topEquiv (F := K) (E := Ω)).symm
    haveI hSgal : IsGalois K ↥(A ⊔ B) := hsupAB.symm ▸ hTopGal
    haveI hSfd : FiniteDimensional K ↥(A ⊔ B) :=
      hsupAB.symm ▸ (inferInstance : FiniteDimensional K ↥(⊤ : IntermediateField K Ω))
    have hcard : Nat.card (Ω ≃ₐ[K] Ω) = Nat.card ((↥A ≃ₐ[K] ↥A) × (↥B ≃ₐ[K] ↥B)) := by
      rw [Nat.card_prod, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
        IsGalois.card_aut_eq_finrank, hfrΩsup]
      have hLD : A.LinearDisjoint ↥B := IntermediateField.LinearDisjoint.of_inf_eq_bot hAB
      rw [IntermediateField.LinearDisjoint.finrank_sup hLD]
    have hbij : Function.Bijective ρ := (Nat.bijective_iff_injective_and_card ρ).mpr ⟨hρinj, hcard⟩
    let φ : (Ω ≃ₐ[K] Ω) ≃* ((↥A ≃ₐ[K] ↥A) × (↥B ≃ₐ[K] ↥B)) := MulEquiv.ofBijective ρ hbij
    have hfst : ∀ σ : Ω ≃ₐ[K] Ω, (φ σ).1 = AlgEquiv.restrictNormalHom A σ := fun σ => rfl
    have hsnd : ∀ σ : Ω ≃ₐ[K] Ω, (φ σ).2 = AlgEquiv.restrictNormalHom B σ := fun σ => rfl
    have hfstA : ∀ σ : Ω ≃ₐ[K] Ω, (φ σ).1 = (ρ σ).1 := fun σ => rfl
    have hfst_mul : ∀ u v : Ω ≃ₐ[K] Ω, (φ (u * v)).1 = (φ u).1 * (φ v).1 := by
      intro u v; simp only [hfstA, map_mul]; rfl
    have hsnd_mul : ∀ u v : Ω ≃ₐ[K] Ω, (φ (u * v)).2 = (φ u).2 * (φ v).2 := by
      intro u v; simp only [hsnd, map_mul]; rfl
    have hfst_zpow : ∀ (u : Ω ≃ₐ[K] Ω) (m : ℤ), (φ (u ^ m)).1 = (φ u).1 ^ m := by
      intro u m
      rw [hfstA, map_zpow]
      exact map_zpow (MonoidHom.fst (↥A ≃ₐ[K] ↥A) (↥B ≃ₐ[K] ↥B)) (ρ u) m
    have hsnd_zpow : ∀ (u : Ω ≃ₐ[K] Ω) (m : ℤ), (φ (u ^ m)).2 = (φ u).2 ^ m := by
      intro u m
      rw [hsnd, map_zpow]
      exact map_zpow (MonoidHom.snd (↥A ≃ₐ[K] ↥A) (↥B ≃ₐ[K] ↥B)) (ρ u) m
    have eAL : ↥A ≃ₐ[K] L := (hArange ▸ (IsScalarTower.toAlgHom K L Ω).equivFieldRange).symm
    set eAuto : (↥A ≃ₐ[K] ↥A) ≃* (L ≃ₐ[K] L) := AlgEquiv.autCongr eAL with heAuto
    set gA : ↥A ≃ₐ[K] ↥A := eAuto.symm g₀ with hgAdef
    have hgAgen : ∀ x : ↥A ≃ₐ[K] ↥A, x ∈ Subgroup.zpowers gA := by
      intro x
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ (eAuto x))
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, eAuto.injective (by
        rw [map_zpow, hgAdef, MulEquiv.apply_symm_apply]
        exact hk)⟩
    have hgAn : gA ^ n = 1 := by
      refine eAuto.injective ?_
      rw [map_pow, map_one, hgAdef, MulEquiv.apply_symm_apply, ← hordg₀]
      exact pow_orderOf_eq_one g₀
    have hgAdvd : orderOf gA ∣ n := orderOf_dvd_iff_pow_eq_one.mpr hgAn
    have hcommA : ∀ x y : ↥A ≃ₐ[K] ↥A, x * y = y * x := by
      intro x y
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgAgen x)
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hgAgen y)
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    have hcommB : ∀ x y : ↥B ≃ₐ[K] ↥B, x * y = y * x := by
      intro x y
      refine (IsPrimitiveRoot.autToPow_injective K hζB).eq_iff.mp ?_
      rw [map_mul, map_mul, mul_comm]
    have hcommΩ : ∀ σ τ : Ω ≃ₐ[K] Ω, σ * τ = τ * σ := by
      intro σ τ
      have h : ρ (σ * τ) = ρ (τ * σ) := by
        rw [map_mul, map_mul]
        exact Prod.ext (hcommA _ _) (hcommB _ _)
      exact hρinj h
    -- the element `δ`
    set δ : Ω ≃ₐ[K] Ω := φ.symm (gA, τB) with hδdef
    have hφδ : φ δ = (gA, τB) := by
      rw [hδdef]; exact MulEquiv.apply_symm_apply φ _
    have hδ1 : (φ δ).1 = gA := by rw [hφδ]
    have hδ2 : (φ δ).2 = τB := by rw [hφδ]
    -- Frobenius elements
    have hΦex : ∀ 𝔭 : s, ∃ Φ : Ω ≃ₐ[K] Ω,
        NK.Chebotarev.IsFrobAtPrime (K := K) (L := Ω)
          (𝔭 : NK.Chebotarev.PrimeIdeal K) Φ :=
      fun 𝔭 => NK.Chebotarev.exists_isFrobAtPrime (K := K) (L := Ω) _
    choose Φ hΦspec using hΦex
    have hPex : ∀ 𝔭 : s, ∃ P : NK.Chebotarev.PrimeIdeal Ω,
        P.asIdeal.LiesOver (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal ∧
          NK.Chebotarev.IsFrobAt (K := K) (L := Ω) P (Φ 𝔭) := hΦspec
    choose P hPspec using hPex
    have hPζ : ∀ 𝔭 : s, (Φ 𝔭) ζ = ζ ^ Ideal.absNorm (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal :=
      fun 𝔭 => isFrobAt_zeta_pow_base M hζprim (𝔭 : NK.Chebotarev.PrimeIdeal K)
        (hM_not_mem 𝔭 𝔭.2) (P 𝔭) (hPspec 𝔭).1 (Φ 𝔭) (hPspec 𝔭).2
    -- the subgroups
    set Hpair : s → Subgroup (Ω ≃ₐ[K] Ω) :=
      fun 𝔭 => closurePairSubgroup δ (Φ 𝔭) (hcommΩ δ (Φ 𝔭)) with hHpair
    set H : Subgroup (Ω ≃ₐ[K] Ω) := ⨅ 𝔭 : s, Hpair 𝔭 with hH
    have hδmemH : δ ∈ H := by
      rw [hH]
      exact Subgroup.mem_iInf.mpr (fun 𝔭 => ⟨1, 0, by simp⟩)
    have hΦmem : ∀ 𝔭 : s, Φ 𝔭 ∈ Hpair 𝔭 := fun 𝔭 => ⟨0, 1, by simp⟩
    have hpair_inf : ∀ 𝔭 : s, Hpair 𝔭 ⊓ B.fixingSubgroup = ⊥ := by
      intro 𝔭
      rw [eq_bot_iff]
      intro h hh
      obtain ⟨i, j, hij⟩ := hh.1
      have hBfix : h ∈ B.fixingSubgroup := hh.2
      subst hij
      rw [Subgroup.mem_bot]
      set χ : ↥B ≃ₐ[K] ↥B := AlgEquiv.restrictNormalHom B (Φ 𝔭) with hχdef
      have hBpart : (φ (δ ^ i * (Φ 𝔭) ^ j)).2 = τB ^ i * χ ^ j := by
        rw [hsnd_mul, hsnd_zpow, hsnd_zpow, hδ2, hsnd, ← hχdef]
      have hBpart0 : τB ^ i * χ ^ j = 1 := by
        rw [← hBpart, hsnd]
        ext y
        rw [AlgEquiv.one_apply, AlgEquiv.restrictNormalHom_apply]
        exact (IntermediateField.mem_fixingSubgroup_iff B _).mp hBfix y y.2
      have hχζ : χ ⟨ζ, hζBmem⟩ = (⟨ζ, hζBmem⟩ : ↥B) ^
          Ideal.absNorm (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal := by
        apply Subtype.ext
        rw [hχdef, AlgEquiv.restrictNormalHom_apply, hPζ 𝔭]
        simp
      have huτ : ((hζB.autToPow K τB : (ZMod M)ˣ) : ZMod M) = (ℓ : ZMod M) :=
        autToPow_eq_of_pow_eq hζB τB ℓ hτB
      have huχ : ((hζB.autToPow K χ : (ZMod M)ˣ) : ZMod M) =
          ((Ideal.absNorm (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal : ℕ) : ZMod M) :=
        autToPow_eq_of_pow_eq hζB χ _ hχζ
      have hid : (n : ℤ) ∣ i ∧ (n : ℤ) ∣ j := by
        have hrelω : (hζB.autToPow K τB) ^ i * (hζB.autToPow K χ) ^ j = 1 := by
          rw [show (hζB.autToPow K τB) ^ i * (hζB.autToPow K χ) ^ j
              = hζB.autToPow K (τB ^ i * χ ^ j) from by rw [map_mul, map_zpow, map_zpow]]
          rw [hBpart0, map_one]
        refine int_dvd_of_zpow_mul_eq_one_base hnpos ?_ ?_ ?_ ?_ ?_ i j hrelω
        · exact (orderOf_pos (hζB.autToPow K τB)).ne'
        · exact (orderOf_pos (hζB.autToPow K χ)).ne'
        · have h1 : ((hζB.autToPow K τB) ^ orderOf (hζB.autToPow K τB)) = 1 :=
            pow_orderOf_eq_one _
          have h2 : ((ℓ : ZMod M)) ^ orderOf (hζB.autToPow K τB) = 1 := by
            have h3 := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) h1
            rw [Units.val_pow_eq_pow_val, Units.val_one, huτ] at h3
            exact h3
          exact (hrel ⟨𝔭, 𝔭.2⟩ _ 0 (by simpa using h2)).1
        · have h1 : ((hζB.autToPow K χ) ^ orderOf (hζB.autToPow K χ)) = 1 :=
            pow_orderOf_eq_one _
          have h2 : ((Ideal.absNorm (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal : ℕ) : ZMod M)
              ^ orderOf (hζB.autToPow K χ) = 1 := by
            have h3 := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) h1
            rw [Units.val_pow_eq_pow_val, Units.val_one, huχ] at h3
            exact h3
          exact (hrel ⟨𝔭, 𝔭.2⟩ 0 _ (by simpa using h2)).2
        · intro i' j' hij'
          have h2 : ((ℓ : ZMod M)) ^ i' *
              ((Ideal.absNorm (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal : ℕ) : ZMod M) ^ j' = 1 := by
            have h3 := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) hij'
            rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
              Units.val_one, huτ, huχ] at h3
            exact h3
          exact hrel ⟨𝔭, 𝔭.2⟩ i' j' h2
      have hgAi : gA ^ i = 1 := by
        rw [← orderOf_dvd_iff_zpow_eq_one]
        exact dvd_trans (by exact_mod_cast hgAdvd) hid.1
      have hgFj : ((φ (Φ 𝔭)).1) ^ j = 1 := by
        have hcardA : Nat.card (↥A ≃ₐ[K] ↥A) = n := by
          rw [IsGalois.card_aut_eq_finrank, hfrA]
        have hord : orderOf ((φ (Φ 𝔭)).1) ∣ n := by
          have h1 : orderOf ((φ (Φ 𝔭)).1) ∣ Fintype.card (↥A ≃ₐ[K] ↥A) := orderOf_dvd_card
          rw [← Nat.card_eq_fintype_card, hcardA] at h1
          exact h1
        rw [← orderOf_dvd_iff_zpow_eq_one]
        exact dvd_trans (by exact_mod_cast hord) hid.2
      have hfirst : (φ (δ ^ i * (Φ 𝔭) ^ j)).1 = 1 := by
        rw [hfst_mul, hfst_zpow, hfst_zpow, hδ1, hgAi, one_mul]
        exact hgFj
      have hsecond : (φ (δ ^ i * (Φ 𝔭) ^ j)).2 = 1 := by
        rw [hsnd_mul, hsnd_zpow, hsnd_zpow, hδ2, hsnd, ← hχdef]
        exact hBpart0
      exact φ.injective (by rw [map_one]; exact Prod.ext hfirst hsecond)
    have hsupH : H ⊔ A.fixingSubgroup = ⊤ := by
      rw [eq_top_iff]
      intro σ _
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgAgen (φ σ).1)
      have hmemN : σ * δ ^ (-k) ∈ A.fixingSubgroup := by
        rw [hkerA, MonoidHom.mem_ker]
        ext x
        rw [AlgEquiv.one_apply, AlgEquiv.restrictNormalHom_apply]
        have h1 : (φ (σ * δ ^ (-k))).1 = 1 := by
          rw [hfst_mul, hfst_zpow, hδ1, ← hk]
          simp
        have h2 := congrArg (fun f : ↥A ≃ₐ[K] ↥A => (f x : Ω)) h1
        rw [hfst] at h2
        rw [AlgEquiv.restrictNormalHom_apply] at h2
        exact h2
      have hσ : σ = (σ * δ ^ (-k)) * δ ^ k := by group
      rw [hσ, Subgroup.sup_eq_closure]
      exact mul_mem (Subgroup.subset_closure (Or.inr hmemN))
        (Subgroup.subset_closure (Or.inl (Subgroup.zpow_mem _ hδmemH k)))
    -- the auxiliary field
    refine ⟨IntermediateField.fixedField H, ?_, ?_⟩
    · rw [disjoint_iff]
      refine le_antisymm ?_ bot_le
      intro x hx
      rw [IntermediateField.mem_inf] at hx
      obtain ⟨hxE, hxA⟩ := hx
      rw [IsGalois.mem_bot_iff_fixed]
      intro σ
      have hσ : σ ∈ H ⊔ A.fixingSubgroup := by rw [hsupH]; trivial
      rw [Subgroup.sup_eq_closure] at hσ
      refine Subgroup.closure_induction (p := fun f _ => f x = x) ?_ ?_ ?_ ?_ hσ
      · intro f hf
        rcases hf with hf | hf
        · exact (IntermediateField.mem_fixedField_iff H x).mp hxE f hf
        · exact (IntermediateField.mem_fixingSubgroup_iff A f).mp hf x hxA
      · exact AlgEquiv.one_apply x
      · intro a b ha hb iha ihb
        rw [AlgEquiv.mul_apply, ihb, iha]
      · intro a _ iha
        exact a.injective (by rw [iha]; simp)
    · intro 𝔭 h𝔭
      haveI hN : (Hpair ⟨𝔭, h𝔭⟩).Normal := ⟨fun {a} ha b => by
        have h : b * a * b⁻¹ = a := by rw [hcommΩ b a, mul_assoc, mul_inv_cancel, mul_one]
        rwa [h]⟩
      refine ⟨IntermediateField.fixedField (Hpair ⟨𝔭, h𝔭⟩), ?_, ?_, ?_⟩
      · exact IntermediateField.fixedField_le (iInf_le Hpair ⟨𝔭, h𝔭⟩)
      · have hjoinK : IntermediateField.fixedField (Hpair ⟨𝔭, h𝔭⟩) ⊔ B = ⊤ := by
          rw [← IntermediateField.fixedField_bot (F := K) (E := Ω), eq_comm,
            IsGalois.fixedField_eq_iff_fixingSubgroup_eq,
            IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_fixedField]
          exact hpair_inf ⟨𝔭, h𝔭⟩
        set S : Set Ω := ((IntermediateField.fixedField (Hpair ⟨𝔭, h𝔭⟩)).restrictScalars ℚ : Set Ω) ∪
          (IntermediateField.adjoin ℚ ({ζ} : Set Ω) : Set Ω) with hSdef
        rw [eq_top_iff]
        intro x _
        rw [IntermediateField.sup_def]
        have hxK : x ∈ IntermediateField.fixedField (Hpair ⟨𝔭, h𝔭⟩) ⊔ B := by rw [hjoinK]; trivial
        rw [IntermediateField.sup_def] at hxK
        revert hxK
        refine IntermediateField.adjoin_induction K (p := fun x _ => x ∈ IntermediateField.adjoin ℚ S)
          ?_ ?_ ?_ ?_ ?_
        · rintro x (hx | hx)
          · exact IntermediateField.subset_adjoin ℚ S (hSdef ▸ Set.mem_union_left _ hx)
          · revert hx
            rw [hB]
            refine IntermediateField.adjoin_induction K
              (p := fun x _ => x ∈ IntermediateField.adjoin ℚ S) ?_ ?_ ?_ ?_ ?_
            · intro y hy
              rw [Set.mem_singleton_iff] at hy
              subst hy
              exact IntermediateField.subset_adjoin ℚ S (hSdef ▸ Set.mem_union_right _
                (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton ζ)))
            · intro c
              exact IntermediateField.subset_adjoin ℚ S (hSdef ▸ Set.mem_union_left _
                ((IntermediateField.mem_restrictScalars ℚ).mpr
                  ((IntermediateField.fixedField (Hpair ⟨𝔭, h𝔭⟩)).algebraMap_mem c)))
            · intro a b _ _ ha hb; exact add_mem ha hb
            · intro a _ ha; exact inv_mem ha
            · intro a b _ _ ha hb; exact mul_mem ha hb
        · intro c
          exact IntermediateField.subset_adjoin ℚ S (hSdef ▸ Set.mem_union_left _
            ((IntermediateField.mem_restrictScalars ℚ).mpr
              ((IntermediateField.fixedField (Hpair ⟨𝔭, h𝔭⟩)).algebraMap_mem c)))
        · intro a b _ _ ha hb; exact add_mem ha hb
        · intro a _ ha; exact inv_mem ha
        · intro a b _ _ ha hb; exact mul_mem ha hb
      · have hres : AlgEquiv.restrictNormalHom (IntermediateField.fixedField (Hpair ⟨𝔭, h𝔭⟩))
            (Φ ⟨𝔭, h𝔭⟩) = 1 := by
          ext y
          rw [AlgEquiv.one_apply, AlgEquiv.restrictNormalHom_apply]
          exact (IntermediateField.mem_fixedField_iff (Hpair ⟨𝔭, h𝔭⟩) (y : Ω)).mp
            y.2 (Φ ⟨𝔭, h𝔭⟩) (hΦmem ⟨𝔭, h𝔭⟩)
        refine ⟨(P ⟨𝔭, h𝔭⟩).under (𝓞 ↥(IntermediateField.fixedField (Hpair ⟨𝔭, h𝔭⟩))), ?_, ?_⟩
        · haveI : (P ⟨𝔭, h𝔭⟩).asIdeal.LiesOver (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal :=
            (hPspec ⟨𝔭, h𝔭⟩).1
          exact Ideal.under_liesOver_of_liesOver
            (B := 𝓞 ↥(IntermediateField.fixedField (Hpair ⟨𝔭, h𝔭⟩)))
            (P ⟨𝔭, h𝔭⟩).asIdeal (𝔭 : NK.Chebotarev.PrimeIdeal K).asIdeal
        · exact hres ▸ (NK.Chebotarev.IsFrobAtRestrictNormalHom
            (IntermediateField.fixedField (Hpair ⟨𝔭, h𝔭⟩)) (hPspec ⟨𝔭, h𝔭⟩).1
            (hPspec ⟨𝔭, h𝔭⟩).2)

end NK.CFTLib.ARL
