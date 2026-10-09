import Mathlib
import Submission.NK.CFTLib.Arl.arl_invariants
import Submission.NK.CFTLib.Arl.arlSetup
import Submission.NK.CFTLib.Existence.arl_dev
import Submission.NK.CFTLib.Existence.artinLawAuxTower
import Submission.NK.CFTLib.ArtinReciprocityIdeal.CyclotomicSubextension
import Submission.NK.CFTLib.ARL.artinReciprocity_cyclotomic
import Submission.NK.CFTLib.Arl.exists_monoidHom_ideleArtin
import Submission.NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust
import Submission.NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin
import Submission.NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one
import Submission.NK.CFTLib.Existence.count_idealOf_ideleInclusion
import Submission.NK.CFTLib.Existence.ideleInclusion_congruenceSubgroup
import Submission.NK.GFC.auxiliaryTower_structure
import Submission.NK.GlobalCFTdeep.SecondInequalitySolvable
import Submission.NK.GlobalCFT.Inclusion.globalCFT_invariants_ideleClassGroup
import Submission.NK.GlobalCFT.Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom
import Submission.NK.GlobalCFT.Cohomology
import Submission.NK.GlobalCFT.NormGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped NumberField Pointwise nonZeroDivisors
open NumberField IntermediateField IsDedekindDomain

noncomputable section

namespace NK.GFC

open NK.GlobalCFT
open NK.GlobalCFT.Inclusion
open NK.CFTLib.Arl

/-! ## The datum form of the arithmetic core, and the `H⁰` assembly, in the language of
subgroups of `Gal(Ω/K)`.

These are verbatim copies of `NK.CFTLib.Arl.exists_art_kills_congruence` and
`NK.CFTLib.Arl.arl_invariants` with the general ideal-theoretic reciprocity law
`NK.CFTLib.ArtinReciprocityIdeal` replaced by the explicit datum `hd` for the single extension
`Ω/Ω^{Nsub}` (which in the application is supplied by the cyclotomic case of the law).
-/

theorem exists_art_kills_congruence_of_datum
    {K Ω : Type} [Field K] [NumberField K] [Field Ω] [NumberField Ω]
    [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal]
    (hMN : Msub ⊔ Nsub = ⊤) (hdisj : Msub ⊓ Nsub = ⊥)
    (hcard : Nat.card ↥Nsub = Nat.card ↥Msub) (hcyc : IsCyclic ↥Nsub)
    (hd : ∃ m : ℕ, 0 < m ∧
      (∀ p : NK.Chebotarev.PrimeIdeal ↥(IntermediateField.fixedField Nsub),
        (m : 𝓞 ↥(IntermediateField.fixedField Nsub)) ∉ p.asIdeal →
        Ideal.ramificationIdxIn p.asIdeal (𝓞 Ω) = 1) ∧
      NK.CFTLib.artinKillsPrincipal ↥(IntermediateField.fixedField Nsub) Ω m) :
    ∃ (M : ℕ) (_ : 0 < M) (u : NK.GlobalCFT.Place ↥(IntermediateField.fixedField Nsub) →
        NK.GlobalCFT.Place K)
      (hu : ∀ w : NK.GlobalCFT.Place ↥(IntermediateField.fixedField Nsub),
        NK.GlobalCFT.Place.LiesOver w (u w))
      (φ : NK.GlobalCFT.Idele K →* NK.GlobalCFT.Idele ↥(IntermediateField.fixedField Nsub))
      (_ : ∀ (x : NK.GlobalCFT.Idele K)
        (w : NK.GlobalCFT.Place ↥(IntermediateField.fixedField Nsub)),
        φ x w = NK.GlobalCFT.Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
      (art : NK.GlobalCFT.Idele ↥(IntermediateField.fixedField Nsub) →*
        Gal(Ω/↥(IntermediateField.fixedField Nsub))),
      (∀ c : (↥(IntermediateField.fixedField Nsub))ˣ,
        art (NK.GlobalCFT.Idele.principalIdele _ c) = 1) ∧
      (∀ y : NK.GlobalCFT.Idele Ω,
        art (NK.GlobalCFT.Idele.normIdeleHom ↥(IntermediateField.fixedField Nsub) Ω y) = 1) ∧
      Function.Surjective art ∧
      (∀ x : NK.GlobalCFT.Idele K, x ∈ NK.CFTLib.Arl.congruenceSubgroup K M →
        art (φ x) = 1) := by
  classical
  obtain ⟨hdisj', hsup', hfrL, hgalL, hgalMid, hcardN, hcardM, hexp, hcommMid, hcycL,
    hcommL⟩ := galoisSetup_of_subgroups Msub Nsub hMN hdisj hcard hcyc
  set L : IntermediateField K Ω := IntermediateField.fixedField Nsub with hLdef
  set Mid : IntermediateField K Ω := IntermediateField.fixedField Msub with hMiddef
  haveI hgalKL : IsGalois K ↥L := by
    rw [hLdef]; exact IsGalois.of_fixedField_normal_subgroup Nsub
  haveI hgalKMid : IsGalois K ↥Mid := by
    rw [hMiddef]; exact IsGalois.of_fixedField_normal_subgroup Msub
  have hdisjL : L ⊓ Mid = ⊥ := by rw [hLdef, hMiddef, inf_comm]; exact hdisj'
  have hsupL : L ⊔ Mid = ⊤ := by rw [hLdef, hMiddef, sup_comm]; exact hsup'
  -- the modulus
  obtain ⟨m, hm, hram, hprinc⟩ := hd
  set mr : ℕ := Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 Ω)) with hmrdef
  have hmr : 0 < mr := by rw [hmrdef]; exact NK.CFTLib.Arl.absNorm_differentIdeal_pos
  set M : ℕ := m * mr with hMdef
  have hMpos : 0 < M := Nat.mul_pos hm hmr
  have hramM : ∀ p : NK.Chebotarev.PrimeIdeal ↥L, (M : 𝓞 ↥L) ∉ p.asIdeal →
      Ideal.ramificationIdxIn p.asIdeal (𝓞 Ω) = 1 := by
    intro p hp
    refine hram p fun hmem => hp ?_
    rw [hMdef, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem
  have hprincM : NK.CFTLib.artinKillsPrincipal ↥L Ω M :=
    NK.CFTLib.artinKillsPrincipal.mono hprinc ⟨mr, by rw [hMdef]⟩
  -- the Artin map
  obtain ⟨U, hU, hadj⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust ↥L M hMpos
  obtain ⟨art, hart, hart_prin, hart_frob, hart_surj⟩ :=
    NK.CFTLib.Arl.exists_monoidHom_ideleArtin hcommL M hMpos hramM hprincM U hU hadj
  have hart_norm : ∀ y : NK.GlobalCFT.Idele Ω,
      art (NK.GlobalCFT.Idele.normIdeleHom ↥L Ω y) = 1 := by
    intro y
    rw [hart]
    exact NK.CFTLib.Arl.normIdeles_mem_ker_of_ideleArtin hcommL M hMpos hramM hprincM U hU hadj
      (NK.NUV2.ARL.normAdjustment (K := ↥L) (L := Ω) M hMpos hramM U hU) y
  -- the idèle inclusion
  obtain ⟨u, hu⟩ : ∃ u : NK.GlobalCFT.Place ↥L → NK.GlobalCFT.Place K,
      ∀ w, NK.GlobalCFT.Place.LiesOver w (u w) :=
    ⟨fun w => Classical.choose (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder w),
      fun w => Classical.choose_spec (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder w)⟩
  obtain ⟨φ, hφ⟩ := NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists u hu
  refine ⟨M, hMpos, u, hu, φ, hφ, art, hart_prin, hart_norm, hart_surj, ?_⟩
  -- the transfer
  intro x hx
  have hUeq : U = NK.CFTLib.Arl.congruenceSubgroup ↥L M :=
    SetLike.ext fun y => (hU.1 y).trans Iff.rfl
  have hφx : φ x ∈ U := by
    rw [hUeq]
    exact NK.CFTLib.Existence.ideleInclusion_congruenceSubgroup u hu φ hφ M x hx
  have hadjU : NK.GlobalCFT.Idele.principalIdele ↥L
      (NK.CFTLib.Arl.adjust U hadj (φ x)) ∈ U := by
    have h1 := NK.CFTLib.Arl.adjust_spec U hadj (φ x)
    have h2 := U.mul_mem (U.inv_mem hφx) h1
    rwa [inv_mul_cancel_left] at h2
  have hcrux : NK.CFTLib.Arl.artinSym hcommL
      (FractionalIdeal.spanSingleton (𝓞 ↥L)⁰
        ((NK.CFTLib.Arl.adjust U hadj (φ x) : Units ↥L) : ↥L)) = 1 :=
    NK.CFTLib.Arl.artinSym_spanSingleton_eq_one hcommL M hMpos hramM hprincM
      _ ((hU.2 _).mp hadjU).1 ((hU.2 _).mp hadjU).2
  have hartφ : art (φ x) = NK.CFTLib.Arl.artinSym hcommL
      (NK.GlobalCFT.Idele.idealOf (φ x)) := by
    rw [hart]
    show NK.CFTLib.Arl.artinSym hcommL
      (NK.GlobalCFT.Idele.idealOf (φ x * NK.GlobalCFT.Idele.principalIdele ↥L
        (NK.CFTLib.Arl.adjust U hadj (φ x)))) = _
    rw [NK.GlobalCFT.Idele.idealOf_mul, NK.GlobalCFT.Idele.idealOf_principalIdele,
      NK.CFTLib.Arl.artinSym_mul hcommL (NK.GlobalCFT.Idele.idealOf_ne_zero _)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero _)), hcrux, mul_one]
  rw [hartφ]
  refine NK.CFTLib.Arl.artinSym_idealOf_ideleInclusion_eq_one (K := K) (L := ↥L) (E := Ω)
    hcommL u hu φ hφ M ?_ x ?_
  · -- the per-prime Frobenius product is trivial
    intro 𝔭 h𝔭M
    have hcardLM : Nat.card Gal(↥L/K) = Nat.card Gal(↥Mid/K) := by
      rw [IsGalois.card_aut_eq_finrank K ↥L, hfrL, hgalMid, ← hcardN, hcard, hcardM]
    have hexpM : ∀ σ : Gal(↥Mid/K), σ ^ Module.finrank K ↥L = 1 := hexp
    have hunrK : ∀ 𝔓 : NK.Chebotarev.PrimeIdeal Ω,
        𝔓.asIdeal.LiesOver 𝔭.asIdeal → 𝔓.asIdeal.ramificationIdx (𝓞 K) = 1 := by
      intro 𝔓 h𝔓
      have h2 : Ideal.ramificationIdxIn 𝔭.asIdeal (𝓞 Ω) = 1 := by
        by_contra hne
        have h3 : ((Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 Ω)) : ℕ) : 𝓞 K) ∈ 𝔭.asIdeal :=
          NK.CFTLib.Arl.absNorm_differentIdeal_mem_of_ramified hne
        refine h𝔭M ?_
        rw [hMdef, Nat.cast_mul]
        exact Ideal.mul_mem_left _ _ h3
      rw [← Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭.asIdeal 𝔓.asIdeal (Gal(Ω/K))]
      exact h2
    exact NK.CFTLib.Arl.prod_frobAtPrime_pow_eq_one_of_unramified L Mid hdisjL hsupL
      hcardLM hexpM 𝔭 hunrK
  · -- the ideal of `φ x` is supported away from `(M)`
    intro 𝔮 h𝔮
    by_contra hmem
    have hx0 : NK.GlobalCFT.Idele.exp (𝔮.under (𝓞 K)) x = 0 :=
      NK.CFTLib.Arl.exp_eq_zero_of_mem_congruence M (NK.CFTLib.Arl.congruenceSubgroup K M)
        ⟨fun y => Iff.rfl, fun b => Iff.rfl⟩ x hx (𝔮.under (𝓞 K)) hmem
    have hcount : (NK.CFTLib.Arl.exps (NK.GlobalCFT.Idele.idealOf (φ x))) 𝔮 ≠ 0 :=
      (Finsupp.mem_support_iff).mp h𝔮
    rw [NK.CFTLib.Arl.exps_apply] at hcount
    rw [NK.CFTLib.Existence.count_idealOf_ideleInclusion u hu φ hφ x (𝔮.under (𝓞 K)) 𝔮
      (by rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal];
          exact Ideal.over_under 𝔮.asIdeal)] at hcount
    rw [NK.GlobalCFT.Idele.count_idealOf, hx0, mul_zero] at hcount
    exact hcount rfl

theorem repInvariants_of_datum
    {K Ω : Type} [Field K] [NumberField K] [Field Ω] [NumberField Ω] [Algebra K Ω]
    [FiniteDimensional K Ω] [IsGalois K Ω]
    (Msub Nsub : Subgroup Gal(Ω/K)) [Msub.Normal] [Nsub.Normal] [Fintype ↥Nsub]
    (hcyc : IsCyclic ↥Nsub) (hMN : Msub ⊔ Nsub = ⊤) (hdisj : Msub ⊓ Nsub = ⊥)
    (hcard : Nat.card ↥Nsub = Nat.card ↥Msub)
    (hd : ∃ m : ℕ, 0 < m ∧
      (∀ p : NK.Chebotarev.PrimeIdeal ↥(IntermediateField.fixedField Nsub),
        (m : 𝓞 ↥(IntermediateField.fixedField Nsub)) ∉ p.asIdeal →
        Ideal.ramificationIdxIn p.asIdeal (𝓞 Ω) = 1) ∧
      NK.CFTLib.artinKillsPrincipal ↥(IntermediateField.fixedField Nsub) Ω m) :
    ∀ a : (NK.GlobalCFT.IdeleClassGroup.rep K Ω).V,
      (∀ g : Gal(Ω/K), (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ g a = a) →
      ∃ b : (NK.GlobalCFT.IdeleClassGroup.rep K Ω).V,
        (∑ n : ↥Nsub, (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ (n : Gal(Ω/K)) b) = a := by
  classical
  intro a ha
  -- ## 0. the Galois setup and the arithmetic core
  obtain ⟨hdisj', hsup', hfrL, hgalL, hgalMid, hcardN, hcardM, hexp, hcommMid, hcycL, hcommL⟩ :=
    NK.CFTLib.Arl.galoisSetup_of_subgroups Msub Nsub hMN hdisj hcard hcyc
  obtain ⟨M, hMpos, u, hu, φ, hφ, art, hart_prin, hart_norm, hart_surj, hart_kill⟩ :=
    NK.GFC.exists_art_kills_congruence_of_datum Msub Nsub hMN hdisj hcard hcyc hd
  haveI hgalKL : IsGalois K ↥(IntermediateField.fixedField Nsub) :=
    IsGalois.of_fixedField_normal_subgroup Nsub
  -- ## 1. the idèle and idèle class group inclusions
  obtain ⟨ψ₁, hψ₁⟩ := globalCFT_ideleClassGroup_inclusion_exists u hu φ hφ
  have hψ₁_inj : Function.Injective ψ₁ :=
    globalCFT_ideleClassGroup_inclusion_injective u hu φ hφ ψ₁ hψ₁
  obtain ⟨u₂, hu₂⟩ : ∃ u₂ : Place Ω → Place ↥(IntermediateField.fixedField Nsub), ∀ w, Place.LiesOver w (u₂ w) :=
    ⟨fun w => Classical.choose (globalCFT_exists_placeUnder w),
      fun w => Classical.choose_spec (globalCFT_exists_placeUnder w)⟩
  obtain ⟨φ₂, hφ₂⟩ := globalCFT_ideleInclusion_exists u₂ hu₂
  obtain ⟨ψ₂, hψ₂⟩ := globalCFT_ideleClassGroup_inclusion_exists u₂ hu₂ φ₂ hφ₂
  have hψ₂_inj : Function.Injective ψ₂ :=
    globalCFT_ideleClassGroup_inclusion_injective u₂ hu₂ φ₂ hφ₂ ψ₂ hψ₂
  have hinv₂ : ∀ q : C[Ω], (∀ σ : Gal(Ω/↥(IntermediateField.fixedField Nsub)), σ • q = q) ↔ q ∈ ψ₂.range :=
    globalCFT_invariants_ideleClassGroup u₂ hu₂ φ₂ hφ₂ ψ₂ hψ₂
  have hinv₁ : ∀ q : C[↥(IntermediateField.fixedField Nsub)], (∀ σ : Gal(↥(IntermediateField.fixedField Nsub)/K), σ • q = q) ↔ q ∈ ψ₁.range :=
    globalCFT_invariants_ideleClassGroup u hu φ hφ ψ₁ hψ₁
  -- ## 2. `a` is `Gal(Ω/K)`-fixed, hence `Gal(Ω/L)`-fixed and in the range of `ψ₂`
  set q : C[Ω] := Additive.toMul a with hq
  have hainv : Additive.ofMul q ∈ (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ.invariants := by
    rw [show Additive.ofMul q = a from by rw [hq]; exact ofMul_toMul a]
    exact (Representation.mem_invariants _ a).mpr ha
  have haq : ∀ σ : Gal(Ω/K), σ • q = q :=
    NK.GlobalCFT.Cohomology.mem_rep_invariants_iff.mp hainv
  have haqL : ∀ σ : Gal(Ω/↥(IntermediateField.fixedField Nsub)), σ • q = q := by
    intro σ
    have key : σ • q = (((IntermediateField.subgroupEquivAlgEquiv Nsub).symm σ : ↥Nsub) :
        Gal(Ω/K)) • q := by
      rw [← MulEquiv.apply_symm_apply (IntermediateField.subgroupEquivAlgEquiv Nsub) σ]
      rfl
    rw [key]
    exact haq _
  obtain ⟨q', hq'⟩ := MonoidHom.mem_range.mp ((hinv₂ q).mp haqL)
  -- ## 3. `q'` is fixed by `Gal(L/K)`
  have hequiv : ∀ (τ : Gal(Ω/K)) (z : C[↥(IntermediateField.fixedField Nsub)]),
      ψ₂ (AlgEquiv.restrictNormalHom ↥(IntermediateField.fixedField Nsub) τ • z) = τ • ψ₂ z := by
    intro τ z
    obtain ⟨v, rfl⟩ := IdeleClassGroup.mk_surjective ↥(IntermediateField.fixedField Nsub) z
    rw [IdeleClassGroup.smul_mk, hψ₂, hψ₂, IdeleClassGroup.smul_mk,
      NK.HassePrinciple.ideleInclusion_smul_restrict u₂ hu₂ φ₂ hφ₂ τ v]
  have hq'fix : ∀ g : Gal(↥(IntermediateField.fixedField Nsub)/K), g • q' = q' := by
    intro g
    obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (K₁ := ↥(IntermediateField.fixedField Nsub))
      Ω g
    have heq : ψ₂ (g • q') = ψ₂ q' := by
      rw [← hτ, hequiv τ q', hq']
      exact haq τ
    exact hψ₂_inj heq
  -- ## 4. `q'` is in the range of the inclusion `C_K → C_L`
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp ((hinv₁ q').mp hq'fix)
  -- ## 5. the arithmetic: `ψ₁ x` is a norm from `C_Ω`
  have hkillι : ∀ w : NK.GlobalCFT.Idele K, art (φ w) = 1 := by
    intro w
    obtain ⟨UK, hUK, hadjK⟩ := NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust K M hMpos
    have hUKeq : UK = NK.CFTLib.Arl.congruenceSubgroup K M :=
      SetLike.ext fun y => (hUK.1 y).trans Iff.rfl
    obtain ⟨b, hb⟩ := hadjK w
    have hb' : w * Idele.principalIdele K b ∈ NK.CFTLib.Arl.congruenceSubgroup K M := by
      rw [← hUKeq]; exact hb
    have h1 := hart_kill (w * Idele.principalIdele K b) hb'
    rw [map_mul, globalCFT_ideleInclusion_principalIdele u hu φ hφ b, map_mul,
      hart_prin] at h1
    simpa using h1
  have hprin_le : Idele.principalSubgroup ↥(IntermediateField.fixedField Nsub) ≤ art.ker := by
    intro c hc
    obtain ⟨b, rfl⟩ := hc
    exact MonoidHom.mem_ker.mpr (hart_prin b)
  let art₁ : C[↥(IntermediateField.fixedField Nsub)] →* Gal(Ω/↥(IntermediateField.fixedField Nsub)) :=
    QuotientGroup.lift (Idele.principalSubgroup ↥(IntermediateField.fixedField Nsub)) art hprin_le
  have hart₁ : ∀ y : NK.GlobalCFT.Idele ↥(IntermediateField.fixedField Nsub), art₁ (IdeleClassGroup.mk ↥(IntermediateField.fixedField Nsub) y) = art y := fun y =>
    QuotientGroup.lift_mk' (Idele.principalSubgroup ↥(IntermediateField.fixedField Nsub)) hprin_le y
  have hsurj₁ : Function.Surjective art₁ := by
    intro g
    obtain ⟨w, hw⟩ := hart_surj g
    exact ⟨IdeleClassGroup.mk ↥(IntermediateField.fixedField Nsub) w, by rw [hart₁, hw]⟩
  have hkerArt : art₁.ker = Idele.normClassSubgroup ↥(IntermediateField.fixedField Nsub) Ω := by
    have hle : Idele.normClassSubgroup ↥(IntermediateField.fixedField Nsub) Ω ≤ art₁.ker := by
      intro z hz
      obtain ⟨y, hy⟩ := Idele.mem_normClassSubgroup.mp hz
      rw [← hy, MonoidHom.mem_ker]
      obtain ⟨v, rfl⟩ := IdeleClassGroup.mk_surjective Ω y
      rw [IdeleClassGroup.normClassHom_mk, hart₁, hart_norm v]
    refine le_antisymm ?_ hle
    have hidxN : (Idele.normClassSubgroup ↥(IntermediateField.fixedField Nsub) Ω).index = Module.finrank ↥(IntermediateField.fixedField Nsub) Ω :=
      NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic
    have hidxker : art₁.ker.index = Nat.card Gal(Ω/↥(IntermediateField.fixedField Nsub)) := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj₁, Subgroup.card_top]
    have hcardG : Nat.card Gal(Ω/↥(IntermediateField.fixedField Nsub)) = Module.finrank ↥(IntermediateField.fixedField Nsub) Ω :=
      IsGalois.card_aut_eq_finrank ↥(IntermediateField.fixedField Nsub) Ω
    have hidx : (Idele.normClassSubgroup ↥(IntermediateField.fixedField Nsub) Ω).index = art₁.ker.index := by
      rw [hidxN, hidxker, hcardG]
    have hne : art₁.ker.index ≠ 0 := by
      rw [hidxker, hcardG]
      exact (Module.finrank_pos (R := ↥(IntermediateField.fixedField Nsub)) (M := Ω)).ne'
    have hrel : (Idele.normClassSubgroup ↥(IntermediateField.fixedField Nsub) Ω).relIndex art₁.ker = 1 := by
      have hmul := Subgroup.relIndex_mul_index hle
      rw [hidx] at hmul
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hne) (by rw [hmul, one_mul])
    exact (Subgroup.relIndex_eq_one (H := Idele.normClassSubgroup ↥(IntermediateField.fixedField Nsub) Ω)
      (K := art₁.ker)).mp hrel
  have hx_norm : ψ₁ x ∈ Idele.normClassSubgroup ↥(IntermediateField.fixedField Nsub) Ω := by
    rw [← hkerArt, MonoidHom.mem_ker]
    obtain ⟨w, rfl⟩ := IdeleClassGroup.mk_surjective K x
    rw [hψ₁ w, hart₁, hkillι w]
  obtain ⟨y, hy⟩ := Idele.mem_normClassSubgroup.mp hx_norm
  -- ## 6. the answer
  refine ⟨Additive.ofMul y, ?_⟩
  have hq_eq : q = ∏ σ : Gal(Ω/↥(IntermediateField.fixedField Nsub)), σ • y := by
    rw [← hq', ← hx, ← hy]
    obtain ⟨v, rfl⟩ := IdeleClassGroup.mk_surjective Ω y
    rw [IdeleClassGroup.normClassHom_mk, hψ₂]
    rw [show (∏ σ : Gal(Ω/↥(IntermediateField.fixedField Nsub)), σ • IdeleClassGroup.mk Ω v)
        = IdeleClassGroup.mk Ω (∏ σ : Gal(Ω/↥(IntermediateField.fixedField Nsub)), σ • v) from by
      have key : ∀ s : Finset (Gal(Ω/↥(IntermediateField.fixedField Nsub))),
          (∏ σ ∈ s, σ • IdeleClassGroup.mk Ω v)
            = IdeleClassGroup.mk Ω (∏ σ ∈ s, σ • v) := by
        intro s
        induction s using Finset.induction with
        | empty => rfl
        | insert a s ha ih =>
            rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, IdeleClassGroup.smul_mk, map_mul]
      simpa using key Finset.univ]
    rw [globalCFT_prod_smul_eq_inclusion_normIdeleHom u₂ hu₂ φ₂ hφ₂ v]
  have hsum : (∑ n : ↥Nsub, (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ (n : Gal(Ω/K))
        (Additive.ofMul y)) = Additive.ofMul q := by
    rw [hq_eq]
    have key : ∀ s : Finset ↥Nsub,
        (∑ n ∈ s, (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ (n : Gal(Ω/K)) (Additive.ofMul y))
          = Additive.ofMul (∏ n ∈ s, (n : Gal(Ω/K)) • y) := by
      intro s
      induction s using Finset.induction with
      | empty => rfl
      | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.prod_insert ha, ih]
          change (Representation.ofMulDistribMulAction (Ω ≃ₐ[K] Ω) (IdeleClassGroup Ω)
              (a : Gal(Ω/K))) (Additive.ofMul y) + Additive.ofMul (∏ n ∈ s, (n : Gal(Ω/K)) • y)
            = Additive.ofMul ((a : Gal(Ω/K)) • y * ∏ n ∈ s, (n : Gal(Ω/K)) • y)
          rw [Representation.ofMulDistribMulAction_apply_apply, toMul_ofMul]
          rfl
    rw [show (∑ n : ↥Nsub, (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ (n : Gal(Ω/K))
          (Additive.ofMul y))
        = ∑ n ∈ (Finset.univ : Finset ↥Nsub),
            (NK.GlobalCFT.IdeleClassGroup.rep K Ω).ρ (n : Gal(Ω/K)) (Additive.ofMul y) from rfl,
      key Finset.univ]
    congr 1
    exact Fintype.prod_equiv (IntermediateField.subgroupEquivAlgEquiv Nsub)
      (fun n : ↥Nsub => (n : Gal(Ω/K)) • y)
      (fun σ : Gal(Ω/↥(IntermediateField.fixedField Nsub)) => σ • y) (fun n => rfl)
  rw [hsum]
  exact (show a = Additive.ofMul q from by rw [hq]; exact ofMul_toMul a).symm


/-- **The arithmetic input of Route B, in its `H⁰` form, from the cyclotomic case of the Artin law.**

Let `K ⊆ L₀, M ⊆ E` be the auxiliary tower of `NK.CFTLib.RouteB.exists_auxiliary_galois_tower`
(`L₀, M` Galois over `K`, `M/K` cyclic, `L₀ ⊓ M = ⊥`, `L₀ ⊔ M = ⊤`, `|Gal(L₀/K)| = |Gal(M/K)|`,
i.e. `[L₀:K] = [M:K]`), and suppose that the auxiliary extension `E/L₀` is a subextension of a
cyclotomic extension of `L₀`: `Ω ⊇ E` with `IsCyclotomicExtension {q} ↥L₀ Ω` and an injective
`↥L₀`-algebra map `φ : E →ₐ[↥L₀] Ω` (this is what
`NK.GFC.exists_auxiliary_galois_tower_cyclotomic` supplies for the tower produced by the Route B
construction, where `M ⊆ K(ζ_q)`).

Then every `Gal(E/K)`-invariant element of the idèle class group `C_E` is a norm for the subgroup
`Gal(E/L₀) ⊆ Gal(E/K)`, i.e. `C_K ⊆ N_{E/L₀}C_E`:

  `∀ a ∈ C_E, (∀ g : Gal(E/K), g • a = a) → ∃ b, ∑_{n ∈ Gal(E/L₀)} n • b = a`.

This is the `H⁰`-form (**') of the arithmetic input of `CFTLib/RouteB/plan.lean`; by
`NK.CFTLib.Translation.inf_range_le_ker_res_of_norm` it is equivalent to the `H²`-form (**)
consumed by `Commons...exists_addOrderOf_eq_of_inf_range_le_ker_res`.  Note this is a statement
*only* about the cyclotomic input: **it does not need the general Artin reciprocity law**.

Route: because `E/L₀` is a subextension of `Ω/L₀`, the *cyclotomic* case of the ideal-theoretic
reciprocity law applies unconditionally
(`NK.CFTLib.artinKillsPrincipal_of_le_isCyclotomicExtension`, base case
`NK.CFTLib.ARL.artinReciprocity_cyclotomic`).  Then

1. the idèlic Artin map `art : 𝕀_{L₀} →* Gal(E/L₀)`, built by
   `NK.CFTLib.Arl.exists_monoidHom_ideleArtin` from the ideal-theoretic law (its `Crux` input
   `artinSym_spanSingleton_eq_one` is exactly that law through the congruence adjustment
   `NK.CFTLib.Arl.exists_isCongruenceSubgroup_and_adjust`), kills the norm idèles: for
   `y : 𝕀_E` one has `art (N y) = ψ(N(ideal y) · (b)) = 1`, with `b ∈ L₀ˣ` the adjustment, using
   `NK.CFTLib.ArtinReciprocityIdeal.frobAtPrime_prod_relNorm_eq_one` (norm ideals have trivial
   Artin symbol) and the law itself (principal ideals of the congruence subgroup);
2. `art` is surjective (Frobenius generation,
   `NK.GlobalCFTdeep.SecondInequality.frobeniusGenerateTop_of_notMem`), and both `ker art` and
   `L₀ˣ · N_{E/L₀} 𝕀_E` have index `[E : L₀]` in `𝕀_{L₀}` (the latter by
   `NK.GlobalCFTdeep.index_eq_finrank_of_isCyclic`, applied to the cyclic extension `E/L₀`);
   hence `ker art = L₀ˣ · N_{E/L₀} 𝕀_E`;
3. for `x ∈ C_K` (read in `C_{L₀}`) one has `art (i x) = ψ(𝔞𝒪_{L₀}) = ψ(𝔞^{[L₀:K]}) = 1` by
   Frobenius functoriality and `|Gal(M/K)| = [L₀:K]` (the case recorded in the guidance of
   `CFTLib/fcElement_of_arl.lean`), so `i x ∈ N_{E/L₀}C_E`;
4. the `H⁰`-computations `C_K ≅ C_E^{Gal(E/K)}` (`Inclusion.globalCFT_invariants_ideleClassGroup`)
   and `ψ(N_{E/L₀} q) = ∏_{n} n • q` (`NK.GlobalCFT.globalCFT_normClassHom_eq_prod_smul`)
   convert this into the stated `H⁰`-form. -/
theorem normImage_of_auxiliary_cyclotomic {K E : Type} [Field K] [NumberField K] [Field E]
    [NumberField E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E]
    (L₀ M : IntermediateField K E) [IsGalois K ↥L₀] [IsGalois K ↥M]
    (hdisj : L₀ ⊓ M = ⊥) (hsup : L₀ ⊔ M = ⊤)
    (hcard : Nat.card (↥L₀ ≃ₐ[K] ↥L₀) = Nat.card (↥M ≃ₐ[K] ↥M))
    (hcyc : IsCyclic (↥M ≃ₐ[K] ↥M)) [Fintype ↥(L₀.fixingSubgroup)]
    (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra ↥L₀ Ω] [IsScalarTower K ↥L₀ Ω]
    [FiniteDimensional ↥L₀ Ω] (q : ℕ) (hq : Nat.Prime q)
    (hcycΩ : IsCyclotomicExtension {q} ↥L₀ Ω) (φ : E →ₐ[↥L₀] Ω) (hφ : Function.Injective φ) :
    ∀ a : (NK.GlobalCFT.IdeleClassGroup.rep K E).V,
      (∀ g : Gal(E/K), (NK.GlobalCFT.IdeleClassGroup.rep K E).ρ g a = a) →
      ∃ b : (NK.GlobalCFT.IdeleClassGroup.rep K E).V,
        (∑ n : ↥(L₀.fixingSubgroup),
          (NK.GlobalCFT.IdeleClassGroup.rep K E).ρ (n : Gal(E/K)) b) = a := by
  classical
  -- the numerical structure of the auxiliary tower
  obtain ⟨-, hfrE, hfrL, hfrEL, -⟩ :=
    NK.GFC.auxiliaryTower_structure L₀ M hdisj hsup hcard hcyc
  -- the Galois-theoretic translation of the field-theoretic hypotheses
  haveI hNormM : (M.fixingSubgroup : Subgroup Gal(E/K)).Normal := inferInstance
  haveI hNormL : (L₀.fixingSubgroup : Subgroup Gal(E/K)).Normal := inferInstance
  have hMN : (M.fixingSubgroup : Subgroup Gal(E/K)) ⊔ L₀.fixingSubgroup = ⊤ :=
    NK.CFTLib.Existence.fixedField_injective _ _
      (by rw [NK.CFTLib.Existence.fixedField_sup_eq_inf, IsGalois.fixedField_fixingSubgroup,
          IsGalois.fixedField_fixingSubgroup, inf_comm, hdisj, IsGalois.fixedField_top])
  have hdisj' : (M.fixingSubgroup : Subgroup Gal(E/K)) ⊓ L₀.fixingSubgroup = ⊥ :=
    NK.CFTLib.Existence.fixedField_injective _ _
      (by rw [NK.CFTLib.Existence.fixedField_inf_eq_sup, IsGalois.fixedField_fixingSubgroup,
          IsGalois.fixedField_fixingSubgroup, sup_comm, hsup, IntermediateField.fixedField_bot])
  have hnpos : 0 < Nat.card (↥L₀ ≃ₐ[K] ↥L₀) := by
    rw [← hfrL]; exact Module.finrank_pos
  have hcard' : Nat.card ↥(L₀.fixingSubgroup) = Nat.card ↥(M.fixingSubgroup) := by
    have h1 : Nat.card ↥(L₀.fixingSubgroup) = Module.finrank ↥L₀ E := by
      rw [Nat.card_congr (IntermediateField.fixingSubgroupEquiv L₀).toEquiv,
        IsGalois.card_aut_eq_finrank ↥L₀ E]
    have h2 : Nat.card ↥(M.fixingSubgroup) = Module.finrank ↥M E := by
      rw [Nat.card_congr (IntermediateField.fixingSubgroupEquiv M).toEquiv,
        IsGalois.card_aut_eq_finrank ↥M E]
    have h3 : Module.finrank ↥M E = Nat.card (↥L₀ ≃ₐ[K] ↥L₀) := by
      have hfrM : Module.finrank K ↥M = Nat.card (↥L₀ ≃ₐ[K] ↥L₀) := by
        rw [← IsGalois.card_aut_eq_finrank K ↥M, ← hcard]
      have htower : Module.finrank K ↥M * Module.finrank ↥M E = Module.finrank K E :=
        Module.finrank_mul_finrank K ↥M E
      rw [hfrM, hfrE] at htower
      exact Nat.eq_of_mul_eq_mul_left hnpos htower
    rw [h1, hfrEL, h2, h3]
  have hcyc' : IsCyclic ↥(L₀.fixingSubgroup) := by
    haveI : IsCyclic (↥M ≃ₐ[K] ↥M) := hcyc
    have hE : IsCyclic Gal(E/↥L₀) :=
      isCyclic_of_injective (NK.CFTLib.Arl.restrictGalEquiv L₀ M)
        (NK.CFTLib.Arl.restrictGalEquiv_injective L₀ M hdisj hsup)
    exact (MulEquiv.isCyclic (IntermediateField.fixingSubgroupEquiv L₀)).mpr hE
  -- the cyclotomic case of the reciprocity law for `E/L₀`
  obtain ⟨m, hm, hram, -, -, hprinc⟩ :=
    NK.CFTLib.Existence.artinLawAuxTower L₀ M hdisj hsup Ω q hq hcycΩ φ hφ
  have hfix : IntermediateField.fixedField (L₀.fixingSubgroup) = L₀ :=
    IsGalois.fixedField_fixingSubgroup L₀
  have hd' : ∃ m : ℕ, 0 < m ∧
      (∀ p : NK.Chebotarev.PrimeIdeal ↥(IntermediateField.fixedField (L₀.fixingSubgroup)),
        (m : 𝓞 ↥(IntermediateField.fixedField (L₀.fixingSubgroup))) ∉ p.asIdeal →
        Ideal.ramificationIdxIn p.asIdeal (𝓞 E) = 1) ∧
      NK.CFTLib.artinKillsPrincipal ↥(IntermediateField.fixedField (L₀.fixingSubgroup)) E m := by
    rw [hfix]
    exact ⟨m, hm, hram, hprinc⟩
  intro a ha
  exact NK.GFC.repInvariants_of_datum (M.fixingSubgroup) (L₀.fixingSubgroup) hcyc' hMN hdisj'
    hcard' hd' a ha


end NK.GFC
