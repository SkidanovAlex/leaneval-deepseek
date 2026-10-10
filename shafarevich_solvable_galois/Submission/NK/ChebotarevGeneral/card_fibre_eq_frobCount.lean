import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Submission.NK.ChebotarevGeneral.Basic
import Submission.NK.ChebotarevGeneral.exists_isFrobAt_liesOver_of_isFrobAtPrime_under
import Submission.NK.ChebotarevGeneral.exists_mem_fixingSubgroup_smul_eq_of_under_eq
import Submission.NK.ChebotarevGeneral.isFrobAtPrime_under_of_isFrobAt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ChebotarevGeneral

noncomputable section

open IsDedekindDomain

set_option linter.unusedSectionVars false

variable {K N : Type} [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
  [FiniteDimensional K N] [IsGalois K N]

/-- **The fibre count.** -/
theorem card_fibre_eq_frobCount (M : IntermediateField K N) {σ : Gal(N/K)}
    (hσ : σ ∈ M.fixingSubgroup) (hfix : M.fixingSubgroup = Subgroup.zpowers σ)
    {𝔭 : NK.Chebotarev.PrimeIdeal K}
    (hunr : ∀ P : NK.Chebotarev.PrimeIdeal N, P.asIdeal.LiesOver 𝔭.asIdeal →
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    Nat.card {𝒬 : NK.Chebotarev.PrimeIdeal ↥M // 𝒬.asIdeal.LiesOver 𝔭.asIdeal ∧
        NK.Chebotarev.IsFrobAtPrime (K := ↥M) (L := N) 𝒬 (M.fixingSubgroupEquiv ⟨σ, hσ⟩) ∧
        𝔭.asIdeal.inertiaDeg' 𝒬.asIdeal = 1}
      = Nat.card {P : NK.Chebotarev.PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal ∧
        NK.Chebotarev.IsFrobAt (K := K) (L := N) P σ} := by
  classical
  have hfinN : Set.Finite {P : NK.Chebotarev.PrimeIdeal N |
      P.asIdeal.LiesOver 𝔭.asIdeal ∧ NK.Chebotarev.IsFrobAt (K := K) (L := N) P σ} :=
    (finite_setOf_liesOver (K := K) (M := N) 𝔭).subset (fun _ hP => hP.1)
  have hfinM : Set.Finite {𝒬 : NK.Chebotarev.PrimeIdeal ↥M |
      𝒬.asIdeal.LiesOver 𝔭.asIdeal ∧
      NK.Chebotarev.IsFrobAtPrime (K := ↥M) (L := N) 𝒬 (M.fixingSubgroupEquiv ⟨σ, hσ⟩) ∧
      𝔭.asIdeal.inertiaDeg' 𝒬.asIdeal = 1} :=
    (finite_setOf_liesOver (K := K) (M := ↥M) 𝔭).subset (fun _ h𝒬 => h𝒬.1)
  haveI : Finite {P : NK.Chebotarev.PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal ∧
      NK.Chebotarev.IsFrobAt (K := K) (L := N) P σ} := hfinN.to_subtype
  haveI : Finite {𝒬 : NK.Chebotarev.PrimeIdeal ↥M // 𝒬.asIdeal.LiesOver 𝔭.asIdeal ∧
      NK.Chebotarev.IsFrobAtPrime (K := ↥M) (L := N) 𝒬 (M.fixingSubgroupEquiv ⟨σ, hσ⟩) ∧
      𝔭.asIdeal.inertiaDeg' 𝒬.asIdeal = 1} := hfinM.to_subtype
  -- descent: `P ↦ P ∩ 𝓞 M`
  have hdesc : ∀ (P : NK.Chebotarev.PrimeIdeal N), P.asIdeal.LiesOver 𝔭.asIdeal →
      NK.Chebotarev.IsFrobAt (K := K) (L := N) P σ →
      (P.under (NumberField.RingOfIntegers ↥M)).asIdeal.LiesOver 𝔭.asIdeal ∧
      NK.Chebotarev.IsFrobAtPrime (K := ↥M) (L := N) (P.under (NumberField.RingOfIntegers ↥M))
        (M.fixingSubgroupEquiv ⟨σ, hσ⟩) ∧
      𝔭.asIdeal.inertiaDeg' (P.under (NumberField.RingOfIntegers ↥M)).asIdeal = 1 := by
    intro P hP hfrob
    obtain ⟨h1, h2⟩ :=
      isFrobAtPrime_under_of_isFrobAt (K := K) (N := N) M hP (hunr P hP) hσ hfrob
    refine ⟨?_, h1, h2⟩
    rw [Ideal.liesOver_iff, IsDedekindDomain.HeightOneSpectrum.under_asIdeal, Ideal.under_under]
    exact hP.over
  let g : {P : NK.Chebotarev.PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal ∧
      NK.Chebotarev.IsFrobAt (K := K) (L := N) P σ} →
      {𝒬 : NK.Chebotarev.PrimeIdeal ↥M // 𝒬.asIdeal.LiesOver 𝔭.asIdeal ∧
      NK.Chebotarev.IsFrobAtPrime (K := ↥M) (L := N) 𝒬 (M.fixingSubgroupEquiv ⟨σ, hσ⟩) ∧
      𝔭.asIdeal.inertiaDeg' 𝒬.asIdeal = 1} :=
    fun P => ⟨P.1.under (NumberField.RingOfIntegers ↥M), hdesc P.1 P.2.1 P.2.2⟩
  -- ascent: `𝒬 ↦ a prime P above 𝒬`
  have hasc : ∀ (𝒬 : NK.Chebotarev.PrimeIdeal ↥M), 𝒬.asIdeal.LiesOver 𝔭.asIdeal →
      NK.Chebotarev.IsFrobAtPrime (K := ↥M) (L := N) 𝒬 (M.fixingSubgroupEquiv ⟨σ, hσ⟩) →
      𝔭.asIdeal.inertiaDeg' 𝒬.asIdeal = 1 →
      ∃ P : NK.Chebotarev.PrimeIdeal N, P.asIdeal.LiesOver 𝒬.asIdeal ∧
        NK.Chebotarev.IsFrobAt (K := K) (L := N) P σ :=
    fun 𝒬 hQ hfrob hf =>
      exists_isFrobAt_liesOver_of_isFrobAtPrime_under (K := K) (N := N) M hQ hf hσ hfrob
  let f : {𝒬 : NK.Chebotarev.PrimeIdeal ↥M // 𝒬.asIdeal.LiesOver 𝔭.asIdeal ∧
      NK.Chebotarev.IsFrobAtPrime (K := ↥M) (L := N) 𝒬 (M.fixingSubgroupEquiv ⟨σ, hσ⟩) ∧
      𝔭.asIdeal.inertiaDeg' 𝒬.asIdeal = 1} →
      {P : NK.Chebotarev.PrimeIdeal N // P.asIdeal.LiesOver 𝔭.asIdeal ∧
        NK.Chebotarev.IsFrobAt (K := K) (L := N) P σ} :=
    fun 𝒬 =>
      ⟨Classical.choose (hasc 𝒬.1 𝒬.2.1 𝒬.2.2.1 𝒬.2.2.2),
        by
          haveI := (Classical.choose_spec (hasc 𝒬.1 𝒬.2.1 𝒬.2.2.1 𝒬.2.2.2)).1
          haveI := 𝒬.2.1
          exact Ideal.LiesOver.trans _ 𝒬.1.asIdeal 𝔭.asIdeal,
        (Classical.choose_spec (hasc 𝒬.1 𝒬.2.1 𝒬.2.2.1 𝒬.2.2.2)).2⟩
  -- injectivity of the ascent map
  have hf_inj : Function.Injective f := by
    intro 𝒬 𝒬' h
    have hc : (Classical.choose (hasc 𝒬.1 𝒬.2.1 𝒬.2.2.1 𝒬.2.2.2) : NK.Chebotarev.PrimeIdeal N) =
        Classical.choose (hasc 𝒬'.1 𝒬'.2.1 𝒬'.2.2.1 𝒬'.2.2.2) :=
      congrArg Subtype.val h
    have h1 := (Classical.choose_spec (hasc 𝒬.1 𝒬.2.1 𝒬.2.2.1 𝒬.2.2.2)).1
    have h2 := (Classical.choose_spec (hasc 𝒬'.1 𝒬'.2.1 𝒬'.2.2.1 𝒬'.2.2.2)).1
    refine Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext ?_)
    rw [h1.over, hc, ← h2.over]
  -- injectivity of the descent map
  have hg_inj : Function.Injective g := by
    intro P P' h
    have hc : P.1.under (NumberField.RingOfIntegers ↥M) =
        P'.1.under (NumberField.RingOfIntegers ↥M) := congrArg Subtype.val h
    obtain ⟨hh, hhh⟩ := exists_mem_fixingSubgroup_smul_eq_of_under_eq hc
    haveI : P.1.asIdeal.LiesOver 𝔭.asIdeal := P.2.1
    -- `hh ∈ Gal(N/M) = ⟨σ⟩ = D_P`, so it fixes `P`
    have hD : (hh : Gal(N/K)) ∈
        Submission.NeukirchUchida.Local.decompositionSubgroup (K := K) P.1 := by
      rw [decompositionSubgroup_eq_zpowers_of_isFrobAt (K := K) (N := N) P.1 σ
        (hunr P.1 P.2.1) P.2.2]
      exact (le_of_eq hfix) hh.2
    have hfixP : (hh : Gal(N/K)) • P.1 = P.1 := by
      rw [smul_primeIdeal_eq_placeSmul]
      rw [Submission.NeukirchUchida.Local.mem_decompositionSubgroup] at hD
      exact hD
    refine Subtype.ext ?_
    rw [← hfixP]
    exact hhh
  -- surjectivity of the descent map
  have hg_surj : Function.Surjective g := by
    intro 𝒬
    obtain ⟨P, hPQ, hPfrob⟩ :=
      exists_isFrobAt_liesOver_of_isFrobAtPrime_under (K := K) (N := N) M 𝒬.2.1 𝒬.2.2.2 hσ 𝒬.2.2.1
    have hPover : P.asIdeal.LiesOver 𝔭.asIdeal := by
      haveI := hPQ
      haveI := 𝒬.2.1
      exact Ideal.LiesOver.trans P.asIdeal 𝒬.1.asIdeal 𝔭.asIdeal
    refine ⟨⟨P, hPover, hPfrob⟩, ?_⟩
    refine Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext ?_)
    rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, ← hPQ.over]
  exact le_antisymm (Nat.card_le_card_of_injective f hf_inj)
    (Nat.card_le_card_of_injective g hg_inj)

end

end NK.ChebotarevGeneral
