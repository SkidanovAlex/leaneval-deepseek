import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.inertiaAtLevelDefs
import Submission.Work.SSGRoute.LevelInertiaProEll.Defs
import Submission.Work.SSGRoute.inertiaSub_image_eq_levelInertia
import Submission.Work.SSGRoute.levelInertiaCardGrowth
import Submission.Work.SSGRoute.LevelInertiaProEll.levelRingBasic
import Submission.Work.SSGRoute.LevelInertiaProEll.levelRingUniformizerData
import Submission.NK.RamificationAudit.Vocab
import Submission.NK.Mine.zmodQuotient_of_orderOf_eq
import Submission.Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
import Submission.Commons.NumberTheory.RamificationInertia.exists_smul_valuationSubringAtPrime_eq
import Submission.NeukirchUchida.Local.PlaceFromValuation
import Submission.NeukirchUchida.Local.DecompositionGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open scoped Pointwise NumberField

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- The automorphism of `𝓞 L` induced by `τ` agrees with the `MulSemiringAction` one. -/
private theorem galRestrict_coe_eq_toRingHom {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (τ : L ≃ₐ[K] L) :
    (galRestrict (𝓞 K) K L (𝓞 L) τ : 𝓞 L →+* 𝓞 L) =
      MulSemiringAction.toRingHom (L ≃ₐ[K] L) (𝓞 L) τ := by
  ext y
  rw [MulSemiringAction.toRingHom_apply]
  change algebraMap (𝓞 L) L (((galRestrict (𝓞 K) K L (𝓞 L)) τ) y) =
    algebraMap (𝓞 L) L (τ • y)
  rw [algebraMap_galRestrict_apply, algebraMap.smul']
  rfl

/-- **The stabiliser of the valuation ring `𝒪_{L,P}` is the stabiliser of the prime ideal `P`.** -/
theorem stabilizerValuationSubringAtPrime {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    MulAction.stabilizer (L ≃ₐ[K] L)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L P) =
      MulAction.stabilizer (L ≃ₐ[K] L) P.asIdeal := by
  ext σ
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have hstab : σ ∈ MulAction.stabilizer (L ≃ₐ[K] L)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L P) := by
      rw [MulAction.mem_stabilizer_iff]; exact h
    have hd : σ ∈ Submission.NeukirchUchida.Local.decompositionSubgroup (K := K) P :=
      (Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
        P σ).mp hstab
    rw [Submission.NeukirchUchida.Local.mem_decompositionSubgroup] at hd
    rw [Ideal.pointwise_smul_def, ← galRestrict_coe_eq_toRingHom,
      ← Submission.NeukirchUchida.Local.placeSmul_asIdeal σ P, hd]
  · intro h
    rw [Ideal.pointwise_smul_def, ← galRestrict_coe_eq_toRingHom] at h
    exact Commons.NumberTheory.RamificationInertia.smul_valuationSubringAtPrime_eq_map_galRestrict
      P P σ h.symm

/-- **Acting trivially modulo `P` on `𝓞 L` is acting trivially on the residue field of the local
ring `𝒪_{L,P}` (equivalently, on `𝒪_{L,P}` modulo its maximal ideal).** -/
theorem idealInertiaValuationBridge {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) (σ : L ≃ₐ[K] L)
    (hσ : σ • P.asIdeal = P.asIdeal) :
    (∀ x : 𝓞 L, σ • x - x ∈ P.asIdeal) ↔
      (∀ y : IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L P,
        (IsDedekindDomain.HeightOneSpectrum.valuation L P) (σ (y : L) - (y : L)) < 1) := by
  set v := IsDedekindDomain.HeightOneSpectrum.valuation L P with hv
  have hmemb : ∀ r : 𝓞 L, (algebraMap (𝓞 L) L) r ∈
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime L P := fun r =>
    (Commons.RingTheory.Valuation.mem_valuationSubringAtPrime P _).mpr
      ⟨r, 1, Submonoid.one_mem _, by simp⟩
  have hle_of : ∀ r : 𝓞 L, v ((algebraMap (𝓞 L) L) r) ≤ 1 := by
    intro r
    rw [← Valuation.mem_valuationSubring_iff,
      ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact hmemb r
  -- the cast of `σ • a` as an element of `L` is `σ` applied to the cast of `a`
  have hcast_apply : ∀ a : 𝓞 L, algebraMap (𝓞 L) L (σ • a) = σ (algebraMap (𝓞 L) L a) := by
    intro a
    have h1 : (σ • a : 𝓞 L) = (galRestrict (𝓞 K) K L (𝓞 L) σ) a :=
      congrArg (fun f : 𝓞 L →+* 𝓞 L => f a)
        (galRestrict_coe_eq_toRingHom (K := K) (L := L) σ).symm
    rw [h1]; exact algebraMap_galRestrict_apply (𝓞 K) σ a
  constructor
  · intro h y
    obtain ⟨a, s, hs, hys⟩ :=
      (Commons.RingTheory.Valuation.mem_valuationSubringAtPrime P (y : L)).mp y.2
    rw [hys]
    set aL : L := algebraMap (𝓞 L) L a with haL
    set sL : L := algebraMap (𝓞 L) L s with hsL
    have ha1 : v (σ aL - aL) < 1 := by
      have hv1 := (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) P
        (σ • a - a)).mpr (h a)
      have hcoe : (↑(σ • a - a) : L) = σ aL - aL := by
        have h1 : ((σ • a - a : 𝓞 L) : L)
            = ((σ • a : 𝓞 L) : L) - ((a : 𝓞 L) : L) := by simp
        have h2 : ((σ • a : 𝓞 L) : L) = σ aL := by
          rw [haL]; simpa using hcast_apply a
        rw [h1, h2, show ((a : 𝓞 L) : L) = aL from haL.symm]
      rw [← hcoe]; exact hv1
    have hs1 : v (σ sL - sL) < 1 := by
      have hv1 := (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) P
        (σ • s - s)).mpr (h s)
      have hcoe : (↑(σ • s - s) : L) = σ sL - sL := by
        have h1 : ((σ • s - s : 𝓞 L) : L)
            = ((σ • s : 𝓞 L) : L) - ((s : 𝓞 L) : L) := by simp
        have h2 : ((σ • s : 𝓞 L) : L) = σ sL := by
          rw [hsL]; simpa using hcast_apply s
        rw [h1, h2, show ((s : 𝓞 L) : L) = sL from hsL.symm]
      rw [← hcoe]; exact hv1
    have hs_notmem : s ∉ P.asIdeal := (Ideal.mem_primeCompl_iff.mp hs)
    have hs0 : s ≠ 0 := fun h0 => hs_notmem (h0 ▸ P.asIdeal.zero_mem)
    have hσs_notmem : (galRestrict (𝓞 K) K L (𝓞 L) σ) s ∉ P.asIdeal := by
      intro hmem
      have hsub : (galRestrict (𝓞 K) K L (𝓞 L) σ) s - s ∈ P.asIdeal := by
        have hh : σ • s - s ∈ P.asIdeal := h s
        have h1 : (σ • s : 𝓞 L) = (galRestrict (𝓞 K) K L (𝓞 L) σ) s :=
          congrArg (fun f : 𝓞 L →+* 𝓞 L => f s)
            (galRestrict_coe_eq_toRingHom (K := K) (L := L) σ).symm
        rwa [h1] at hh
      exact hs_notmem (by simpa using sub_mem hmem hsub)
    have hsL_eq : v sL = 1 :=
      (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem P).mpr hs_notmem
    have hσsL_eq : v (σ sL) = 1 := by
      have hcast : σ sL = algebraMap (𝓞 L) L ((galRestrict (𝓞 K) K L (𝓞 L) σ) s) :=
        (algebraMap_galRestrict_apply (𝓞 K) σ s).symm
      rw [hcast]
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem P).mpr hσs_notmem
    have hsL_ne : sL ≠ 0 := by
      rw [hsL]; exact fun h0 => hs0 ((NumberField.RingOfIntegers.coe_injective (K := L)) (by simpa using h0))
    have hσsL_ne : σ sL ≠ 0 := fun h0 => hsL_ne (σ.injective (by rw [h0, map_zero]))
    have hs1' : v (sL - σ sL) < 1 := by
      rw [show sL - σ sL = -(σ sL - sL) from by ring, Valuation.map_neg]; exact hs1
    have hnum : v (σ aL * sL - aL * σ sL) < 1 := by
      have hsplit : σ aL * sL - aL * σ sL = (σ aL - aL) * sL + aL * (sL - σ sL) := by ring
      rw [hsplit]
      refine Valuation.map_add_lt v ?_ ?_
      · rw [map_mul]
        calc v (σ aL - aL) * v sL ≤ v (σ aL - aL) * 1 := by
              gcongr; exact hle_of s
          _ = v (σ aL - aL) := mul_one _
          _ < 1 := ha1
      · rw [map_mul]
        calc v aL * v (sL - σ sL) ≤ 1 * v (sL - σ sL) := by
              gcongr; exact hle_of a
          _ = v (sL - σ sL) := one_mul _
          _ < 1 := hs1'
    have hden : v (σ sL * sL) = 1 := by rw [map_mul, hσsL_eq, hsL_eq, one_mul]
    have hkey : σ (aL * sL⁻¹) - aL * sL⁻¹
        = (σ aL * sL - aL * σ sL) / (σ sL * sL) := by
      rw [map_mul, map_inv₀, div_eq_mul_inv]
      field_simp
    rw [hkey, Valuation.map_div, hden, div_one]
    exact hnum
  · intro h x
    apply (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) P
      (σ • x - x)).mp
    have hcast : algebraMap (𝓞 L) L (σ • x - x)
        = σ (algebraMap (𝓞 L) L x) - algebraMap (𝓞 L) L x := by
      rw [map_sub, hcast_apply x]
    change (IsDedekindDomain.HeightOneSpectrum.valuation L P)
      (algebraMap (𝓞 L) L (σ • x - x)) < 1
    rw [hcast]
    exact h ⟨algebraMap (𝓞 L) L x, hmemb x⟩

private theorem inertiaSubgroup_map_subtype_eq_idealInertia
    {k Ω : Type*} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M]
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥M)) :
    ((IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P).inertiaSubgroup k).map
        ((IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P).decompositionSubgroup
          k).subtype
      = Ideal.inertia (↥M ≃ₐ[k] ↥M) P.asIdeal := by
  classical
  haveI hgal : IsGalois k ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  set B : ValuationSubring ↥M :=
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M P with hB
  have hD : B.decompositionSubgroup k = MulAction.stabilizer (↥M ≃ₐ[k] ↥M) P.asIdeal := by
    rw [hB]; exact stabilizerValuationSubringAtPrime P
  -- The elementwise dictionary: for `σ` in the decomposition subgroup of `B`, acting trivially on
  -- the residue field of `B` is the same as acting trivially modulo `P` on `𝓞 ↥M`.
  have key : ∀ σ : B.decompositionSubgroup k,
      σ ∈ B.inertiaSubgroup k ↔
        (σ : ↥M ≃ₐ[k] ↥M) ∈ Ideal.inertia (↥M ≃ₐ[k] ↥M) P.asIdeal := by
    intro σ
    have hσstab : (σ : ↥M ≃ₐ[k] ↥M) ∈ MulAction.stabilizer (↥M ≃ₐ[k] ↥M) P.asIdeal := by
      rw [← hD]; exact σ.2
    have hspecσ : (σ : ↥M ≃ₐ[k] ↥M) • P.asIdeal = P.asIdeal :=
      MulAction.mem_stabilizer_iff.mp hσstab
    -- `G_0` of the ramification filtration is the inertia subgroup of a valuation subring.
    have h1 : σ ∈ B.inertiaSubgroup k ↔
        ∀ x : B, σ • x - x ∈ IsLocalRing.maximalIdeal B := by
      rw [← NK.Ramification.ramificationSubgroup_zero (K := k) B]
      simpa using (NK.Ramification.mem_ramificationSubgroup_iff B 0 σ)
    have h2 : (σ : ↥M ≃ₐ[k] ↥M) ∈ Ideal.inertia (↥M ≃ₐ[k] ↥M) P.asIdeal ↔
        ∀ x : 𝓞 ↥M, (σ : ↥M ≃ₐ[k] ↥M) • x - x ∈ P.asIdeal :=
      AddSubgroup.mem_inertia
    -- The maximal ideal of `B` is described by the `P`-adic valuation, which is equivalent to the
    -- canonical valuation of the valuation subring `B`.
    have hequiv : B.valuation.IsEquiv (IsDedekindDomain.HeightOneSpectrum.valuation ↥M P) :=
      (Valuation.isEquiv_iff_valuationSubring _ _).mpr (by
        rw [ValuationSubring.valuationSubring_valuation,
          ← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring])
    have hval : ∀ y : B, σ • y - y ∈ IsLocalRing.maximalIdeal B ↔
        (IsDedekindDomain.HeightOneSpectrum.valuation ↥M P)
          ((σ : ↥M ≃ₐ[k] ↥M) (y : ↥M) - (y : ↥M)) < 1 := by
      intro y
      rw [ValuationSubring.valuation_lt_one_iff]
      rw [show ((σ • y - y : B) : ↥M) =
          (σ : ↥M ≃ₐ[k] ↥M) (y : ↥M) - (y : ↥M) from by
        simp [NK.Ramification.coe_smul]]
      exact hequiv.lt_one_iff_lt_one
    have hbridge := idealInertiaValuationBridge (K := k) (L := ↥M) P (σ : ↥M ≃ₐ[k] ↥M) hspecσ
    rw [h1, h2]
    simp only [hval]
    exact hbridge.symm
  have hKeq : B.inertiaSubgroup k =
      (Ideal.inertia (↥M ≃ₐ[k] ↥M) P.asIdeal).subgroupOf (B.decompositionSubgroup k) := by
    ext σ
    rw [Subgroup.mem_subgroupOf]
    exact key σ
  rw [hKeq, AddSubgroup.subgroupOf_inertia, AddSubgroup.inertia_map_subtype, hD]
  exact inf_eq_left.mpr (Ideal.inertia_le_stabilizer P.asIdeal)

theorem levelRingInertiaIdent_axf
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M] :
    ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k =
        MulAction.stabilizer (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal) ∧
    (((A.comap (algebraMap ↥M Ω)).inertiaSubgroup k).map
        ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype =
      Ideal.inertia (↥M ≃ₐ[k] ↥M) (Work.SSGRoute.levelPrime k Ω A hA M).asIdeal) := by
  classical
  haveI hgal : IsGalois k ↥M := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  -- `A ∩ M` is the localisation of `𝓞 ↥M` at the level prime `P`
  have hspec : A.comap (algebraMap ↥M Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥M
        (Work.SSGRoute.levelPrime k Ω A hA M) :=
    NK.Reconstruct.primeOfLevel_spec A M (NK.Reconstruct.comap_level_ne_top hA M)
  have hgoal := inertiaSubgroup_map_subtype_eq_idealInertia M
    (Work.SSGRoute.levelPrime k Ω A hA M)
  constructor
  · rw [hspec]
    exact stabilizerValuationSubringAtPrime (Work.SSGRoute.levelPrime k Ω A hA M)
  · rwa [← hspec] at hgoal


theorem levelInertiaNormalProEll_axf
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : _root_.SSGRoute.IsFinPlace k A)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M] :
    ∃ (W : Subgroup (↥M ≃ₐ[k] ↥M)) (ℓ a : ℕ),
      W ≤ Work.SSGRoute.levelInertiaOf k Ω A hA M ∧
      (∀ δ ∈ Work.SSGRoute.levelInertiaOf k Ω A hA M, ∀ u ∈ W, δ * u * δ⁻¹ ∈ W) ∧
      ℓ.Prime ∧ ℓ ≠ p ∧ Nat.card W = ℓ ^ a ∧
      (∃ g ∈ Work.SSGRoute.levelInertiaOf k Ω A hA M,
        ∀ δ ∈ Work.SSGRoute.levelInertiaOf k Ω A hA M,
          ∃ m : ℤ, δ⁻¹ * g ^ m ∈ W) := by
  classical
  obtain ⟨hdvr, hnoeth, hperf, hfinres, ⟨ℓ, f, hℓprime, hℓne, hℓcard⟩⟩ :=
    LevelInertiaProEll.levelRingBasic p k Ω A hA h M
  haveI : IsDiscreteValuationRing (A.comap (algebraMap ↥M Ω)) := hdvr
  haveI : IsNoetherianRing (A.comap (algebraMap ↥M Ω)) := hnoeth
  haveI : PerfectField (IsLocalRing.ResidueField (A.comap (algebraMap ↥M Ω))) := hperf
  haveI : Finite (IsLocalRing.ResidueField (A.comap (algebraMap ↥M Ω))) := hfinres
  haveI hgal : IsGalois k ↥M := inferInstance
  haveI hGfin : Fintype (↥M ≃ₐ[k] ↥M) := AlgEquiv.fintype k ↥M
  haveI hDfin : Finite ↥((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k) :=
    Finite.of_injective
      (fun x : ↥((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k) => (x : ↥M ≃ₐ[k] ↥M))
      Subtype.val_injective
  obtain ⟨π, E, hD⟩ := LevelInertiaProEll.levelRingUniformizerData p k Ω A hA h M
  have hident := levelRingInertiaIdent_axf p k Ω A hA h M
  obtain ⟨N₀, hN₀⟩ :=
    NK.RamificationAudit.exists_ramificationSubgroup_eq_bot_of_isDiscreteValuationRing
      (K := k) (A.comap (algebraMap ↥M Ω))
  have hbot : NK.Ramification.ramificationSubgroup (K := k)
      (A.comap (algebraMap ↥M Ω)) (1 + N₀) = ⊥ :=
    le_bot_iff.mp (hN₀ ▸ NK.Ramification.ramificationSubgroup_antitone
      (A.comap (algebraMap ↥M Ω)) (Nat.le_add_left N₀ 1))
  obtain ⟨j, hj⟩ := NK.RamificationDeep.exists_natCard_one_eq_prime_pow (K := k) hD
    hℓprime hℓcard hbot
  -- the residue field of the level ring is a finite field, so its units are cyclic
  haveI hfinQ : Finite ((A.comap (algebraMap ↥M Ω)) ⧸
      IsLocalRing.maximalIdeal (A.comap (algebraMap ↥M Ω))) := hfinres
  haveI hcycU : IsCyclic (((A.comap (algebraMap ↥M Ω)) ⧸
      IsLocalRing.maximalIdeal (A.comap (algebraMap ↥M Ω)))ˣ) := instIsCyclicUnitsOfFinite
  have hcyc := NK.RamificationDeep.isCyclic_quotient_ramificationSubgroup (K := k)
    (A.comap (algebraMap ↥M Ω)) π E hD hcycU
  refine ⟨(NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 1).map
      ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype, ℓ, j, ?_, ?_, hℓprime,
    hℓne, ?_, ?_⟩
  · calc (NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 1).map
          ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype
        ≤ ((A.comap (algebraMap ↥M Ω)).inertiaSubgroup k).map
            ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype :=
          Subgroup.map_mono (NK.Ramification.ramificationSubgroup_le_inertiaSubgroup
            (A.comap (algebraMap ↥M Ω)) 1)
      _ = Ideal.inertia (↥M ≃ₐ[k] ↥M) (levelPrime k Ω A hA M).asIdeal := hident.2
      _ = levelInertiaOf k Ω A hA M := rfl
  · intro δ hδ u hu
    have hδ' : δ ∈ ((A.comap (algebraMap ↥M Ω)).inertiaSubgroup k).map
        ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype := hident.2.symm ▸ hδ
    obtain ⟨δ₀, _, hδ₀eq⟩ := Subgroup.mem_map.mp hδ'
    obtain ⟨u₀, hu₀mem, hu₀eq⟩ := Subgroup.mem_map.mp hu
    have hconj : δ₀ * u₀ * δ₀⁻¹ ∈
        NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 1 :=
      (NK.Ramification.ramificationSubgroup_normal (A.comap (algebraMap ↥M Ω)) 1).conj_mem
        u₀ hu₀mem δ₀
    refine Subgroup.mem_map.mpr ⟨δ₀ * u₀ * δ₀⁻¹, hconj, ?_⟩
    simp only [map_mul, map_inv, hδ₀eq, hu₀eq]
  · rw [Subgroup.card_map_of_injective
      (K := NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 1)
      (f := ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype) Subtype.val_injective,
      hj]
  · -- cyclicity of the quotient: exhibit a generator modulo the wild inertia
    change ∃ g ∈ Ideal.inertia (↥M ≃ₐ[k] ↥M) (levelPrime k Ω A hA M).asIdeal,
      ∀ δ ∈ Ideal.inertia (↥M ≃ₐ[k] ↥M) (levelPrime k Ω A hA M).asIdeal,
        ∃ m : ℤ, δ⁻¹ * g ^ m ∈
          (NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 1).map
            ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype
    have hG0eq : (NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 0).map
        ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype =
        Ideal.inertia (↥M ≃ₐ[k] ↥M) (levelPrime k Ω A hA M).asIdeal := by
      rw [NK.Ramification.ramificationSubgroup_zero]
      exact hident.2
    obtain ⟨q, hq⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
    obtain ⟨g₀, hg₀⟩ := QuotientGroup.mk'_surjective
      ((NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 1).subgroupOf
        (NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 0)) q
    refine ⟨((g₀ : ↥((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k)) : ↥M ≃ₐ[k] ↥M),
      hG0eq ▸ Subgroup.mem_map_of_mem
        (((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype) g₀.2, fun δ hδ => ?_⟩
    have hδ' : δ ∈ (NK.Ramification.ramificationSubgroup (K := k)
        (A.comap (algebraMap ↥M Ω)) 0).map
        ((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k).subtype := hG0eq.symm ▸ hδ
    obtain ⟨δ₀, hδ₀G0, hδ₀eq⟩ := Subgroup.mem_map.mp hδ'
    have hz : QuotientGroup.mk' ((NK.Ramification.ramificationSubgroup (K := k)
          (A.comap (algebraMap ↥M Ω)) 1).subgroupOf
          (NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 0))
        (⟨δ₀, hδ₀G0⟩ : ↥(NK.Ramification.ramificationSubgroup (K := k)
          (A.comap (algebraMap ↥M Ω)) 0)) ∈ Subgroup.zpowers q := by
      rw [hq]; exact Subgroup.mem_top _
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨m, ?_⟩
    set x : ↥(NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 0) :=
      (⟨δ₀, hδ₀G0⟩ : ↥(NK.Ramification.ramificationSubgroup (K := k)
        (A.comap (algebraMap ↥M Ω)) 0))⁻¹ * g₀ ^ m with hxdef
    have h1 : (QuotientGroup.mk' ((NK.Ramification.ramificationSubgroup (K := k)
          (A.comap (algebraMap ↥M Ω)) 1).subgroupOf
          (NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 0))) x = 1 := by
      rw [hxdef, map_mul, map_inv, map_zpow, hg₀, ← hm, inv_mul_cancel]
    have hx : x ∈ (NK.Ramification.ramificationSubgroup (K := k)
        (A.comap (algebraMap ↥M Ω)) 1).subgroupOf
        (NK.Ramification.ramificationSubgroup (K := k) (A.comap (algebraMap ↥M Ω)) 0) := by
      have h2 : x ∈ (QuotientGroup.mk' ((NK.Ramification.ramificationSubgroup (K := k)
            (A.comap (algebraMap ↥M Ω)) 1).subgroupOf
            (NK.Ramification.ramificationSubgroup (K := k)
              (A.comap (algebraMap ↥M Ω)) 0))).ker := MonoidHom.mem_ker.mpr h1
      rwa [QuotientGroup.ker_mk'] at h2
    refine Subgroup.mem_map.mpr ⟨(x : ↥((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k)),
      Subgroup.mem_subgroupOf.mp hx, ?_⟩
    have hxval : (x : ↥((A.comap (algebraMap ↥M Ω)).decompositionSubgroup k)) = δ₀⁻¹ * g₀ ^ m := by
      rw [hxdef]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
    rw [hxval, map_mul, map_inv, map_zpow, hδ₀eq]
    rfl



/-! ## Group theory: a finite cyclic group of order divisible by `p ^ n` has a surjection onto
`ZMod (p ^ n)` -/

/-- A group generated by `g` whose order is divisible by `p ^ n` admits a surjection onto the
cyclic group `Multiplicative (ZMod (p ^ n))`. -/
theorem cyclic_zmod_surjective {H : Type*} [Group H] {p n : ℕ} (hp : p.Prime)
    (g : H) (hg : ∀ x : H, x ∈ Subgroup.zpowers g) (hdiv : p ^ n ∣ orderOf g) :
    ∃ χ : H →* Multiplicative (ZMod (p ^ n)), Function.Surjective χ := by
  classical
  have hex : ∀ x : H, ∃ k : ℤ, g ^ k = x := fun x => Subgroup.mem_zpowers_iff.mp (hg x)
  choose e he using hex
  have hkey : ∀ k l : ℤ, g ^ k = g ^ l → ((k : ZMod (p ^ n)) = (l : ZMod (p ^ n))) := by
    intro k l hkl
    have h1 : g ^ (k - l) = 1 := by rw [zpow_sub, hkl, mul_inv_cancel]
    have h2 : ((orderOf g : ℕ) : ℤ) ∣ (k - l) :=
      (orderOf_dvd_iff_zpow_eq_one (x := g) (i := k - l)).mpr h1
    have h3 : (((p ^ n : ℕ)) : ℤ) ∣ (k - l) :=
      dvd_trans (by exact_mod_cast hdiv) h2
    rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd,
      show (l - k : ℤ) = -(k - l) from by ring]
    exact dvd_neg.mpr h3
  refine ⟨MonoidHom.mk' (fun x => Multiplicative.ofAdd ((e x : ℤ) : ZMod (p ^ n))) ?_, ?_⟩
  · intro x y
    have hx : g ^ (e x) = x := he x
    have hy : g ^ (e y) = y := he y
    have hxy : g ^ (e (x * y)) = x * y := he (x * y)
    have hsum : g ^ (e x + e y) = x * y := by rw [zpow_add, hx, hy]
    have heq : g ^ (e (x * y)) = g ^ (e x + e y) := by rw [hxy, hsum]
    have hk := hkey (e (x * y)) (e x + e y) heq
    show Multiplicative.ofAdd (((e (x * y) : ℤ) : ZMod (p ^ n)))
        = Multiplicative.ofAdd (((e x : ℤ) : ZMod (p ^ n)))
          * Multiplicative.ofAdd (((e y : ℤ) : ZMod (p ^ n)))
    rw [← ofAdd_add, ← Int.cast_add]
    exact congrArg Multiplicative.ofAdd hk
  · intro y
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective y.toAdd
    refine ⟨g ^ a, ?_⟩
    have hga : g ^ (e (g ^ a)) = g ^ a := he (g ^ a)
    have hk := hkey (e (g ^ a)) a hga
    show Multiplicative.ofAdd (((e (g ^ a) : ℤ) : ZMod (p ^ n))) = y
    rw [hk, ha]
    rfl

/-- The level inertia group at a finite level with order divisible by `p ^ n` has a surjection
onto `Multiplicative (ZMod (p ^ n))`. -/
theorem levelInertia_quotient
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1)
    (M : IntermediateField k Ω) [FiniteDimensional k M] [Normal k M] [NumberField ↥M] (n : ℕ)
    (hdiv : p ^ n ∣ Nat.card ↥(levelInertiaOf k Ω A hA M)) :
    ∃ χ : ↥(levelInertiaOf k Ω A hA M) →* Multiplicative (ZMod (p ^ n)),
      Function.Surjective χ := by
  have hp := Fact.out (p := p.Prime)
  obtain ⟨W, ℓ, a, hWle, hWnorm, hℓprime, hℓne, hWcard, g, hgmem, hgen⟩ :=
    levelInertiaNormalProEll_axf p k Ω A hA h M
  set G := levelInertiaOf k Ω A hA M with hG
  set W' : Subgroup G := W.subgroupOf G with hW'def
  haveI hW'N : W'.Normal := ⟨fun n hn x => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hWnorm x x.2 n hn⟩
  have hcardW : Nat.card ↥W' = ℓ ^ a := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWle).toEquiv, hWcard]
  have hcardG : Nat.card ↥W' * Nat.card (G ⧸ W') = Nat.card G := by
    rw [← Subgroup.index_eq_card]; exact Subgroup.card_mul_index W'
  have hcop : Nat.Coprime (p ^ n) (Nat.card ↥W') := by
    rw [hcardW]
    have hpℓ : Nat.Coprime p ℓ :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr
        (fun hd => hℓne ((Nat.prime_dvd_prime_iff_eq hp hℓprime).mp hd).symm)
    exact (hpℓ.pow_left n).pow_right a
  have hdiv' : p ^ n ∣ Nat.card (G ⧸ W') :=
    Nat.Coprime.dvd_of_dvd_mul_left hcop (hcardG ▸ hdiv)
  have hq : ∀ x : G ⧸ W', x ∈ Subgroup.zpowers (QuotientGroup.mk' W' (⟨g, hgmem⟩ : G)) := by
    intro x
    obtain ⟨δ, rfl⟩ := QuotientGroup.mk'_surjective W' x
    obtain ⟨m', hm'⟩ := hgen δ δ.2
    refine Subgroup.mem_zpowers_iff.mpr ⟨m', ?_⟩
    have h1 : (QuotientGroup.mk' W') (δ⁻¹ * (⟨g, hgmem⟩ : G) ^ m') = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (by rw [Subgroup.mem_subgroupOf]; exact hm')
    have h2 : (QuotientGroup.mk' W' δ)⁻¹
        * (QuotientGroup.mk' W' (⟨g, hgmem⟩ : G)) ^ m' = 1 := by
      rw [← map_inv, ← map_zpow, ← map_mul]
      exact h1
    have h3 := congrArg (fun z => (QuotientGroup.mk' W' δ) * z) h2
    simpa using h3
  have hordq : orderOf (QuotientGroup.mk' W' (⟨g, hgmem⟩ : G)) = Nat.card (G ⧸ W') :=
    orderOf_eq_card_of_forall_mem_zpowers hq
  have hdiv_ord : p ^ n ∣ orderOf (QuotientGroup.mk' W' (⟨g, hgmem⟩ : G)) := by
    rw [hordq]; exact hdiv'
  obtain ⟨χ, hχ⟩ := cyclic_zmod_surjective hp _ hq hdiv_ord
  exact ⟨χ.comp (QuotientGroup.mk' W'), hχ.comp (QuotientGroup.mk'_surjective W')⟩

theorem inertia_power_quotients
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1) (n : ℕ) :
    ∃ χ : ↥(SSGRoute.inertiaSub k Ω A) →* Multiplicative (ZMod (p ^ n)),
      Function.Surjective χ := by
  obtain ⟨M, hfd, hnorm, hnf, hdiv⟩ := levelInertiaCardGrowth p k Ω A hA h n
  haveI := hfd
  haveI := hnorm
  haveI := hnf
  obtain ⟨χM, hχM⟩ := levelInertia_quotient p k Ω A hA h M n hdiv
  let ρ' : ↥(SSGRoute.inertiaSub k Ω A) →* ↥(levelInertiaOf k Ω A hA M) :=
    ((AlgEquiv.restrictNormalHom M).comp (SSGRoute.inertiaSub k Ω A).subtype).codRestrict _
      (by
        intro x
        have hx : (AlgEquiv.restrictNormalHom M) ((SSGRoute.inertiaSub k Ω A).subtype x) ∈
            (SSGRoute.inertiaSub k Ω A).map (AlgEquiv.restrictNormalHom M) :=
          Subgroup.mem_map.mpr ⟨(x : Ω ≃ₐ[k] Ω), x.2, rfl⟩
        rwa [inertiaSub_image_eq_levelInertia k Ω A hA M] at hx)
  have hρ'surj : Function.Surjective ρ' := by
    intro y
    have hy : (y : ↥M ≃ₐ[k] ↥M) ∈
        (SSGRoute.inertiaSub k Ω A).map (AlgEquiv.restrictNormalHom M) := by
      rw [inertiaSub_image_eq_levelInertia k Ω A hA M]; exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact ⟨χM.comp ρ', hχM.comp hρ'surj⟩

end Work.SSGRoute.PT
