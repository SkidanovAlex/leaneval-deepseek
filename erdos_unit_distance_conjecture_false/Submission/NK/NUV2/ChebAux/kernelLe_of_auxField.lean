import Mathlib
import Submission.NK.CFTLib.ARL.AuxField
import Submission.NK.CFTLib.ArtinReciprocityIdeal.cyclotomicKernelLe
import Submission.NK.CFTLib.ArtinReciprocityIdeal.normRayLeKer
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSymSurjectiveOnCoprime
import Submission.NK.CFTLib.ArtinReciprocityIdeal.LangDefs
import Submission.NK.CFTLib.ArtinReciprocityIdeal.relNormUnit_trans
import Submission.NK.CFTLib.ArtinReciprocityIdeal.norm_principalRay_le
import Submission.NK.CFTLib.ArtinReciprocityIdeal.mem_idealCoprimeGroup_iff
import Submission.NK.CFTLib.ARL.cyclotomicCellKernelLe_B
import Submission.NK.CFTLib.ARLAlt.CellAbelian
import Submission.NK.CFTLib.ARLAlt.AuxLocal
import Submission.NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension
import Submission.NK.Chebotarev.IsFrobAtPrimeAlgEquivSameBase
import Submission.NK.Chebotarev.ExistsUniqueIsFrobAtPrime
import Submission.NK.CFTLib.ARLAlt.Descent
import Submission.NK.CFTLib.ARLAlt.CellAtAux
import Submission.NK.CFTLib.ARL.kernelLe_of_auxField_B
import Submission.NK.Existence.ArtinLemma.helpers
import Submission.NK.CFTLib.ArtinReciprocityIdeal.indexIdealCoprimeLeNormClassIndex

namespace NK.NUV2.ChebAux

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors IsMulCommutative

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

noncomputable section

/-! ## Transport of the Artin symbol along a `K`-isomorphism -/

/-- The chosen Frobenius at any prime is a Frobenius element (no unramifiedness needed). -/
theorem isFrobAtPrime_frobAtPrime' {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : NK.Chebotarev.PrimeIdeal K) :
    NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) p
      (NK.Chebotarev.frobAtPrime (K := K) (L := L) p) := by
  rw [NK.Chebotarev.frobAtPrime,
    dif_pos (NK.Chebotarev.exists_isFrobAtPrime (K := K) (L := L) p)]
  exact (NK.Chebotarev.exists_isFrobAtPrime (K := K) (L := L) p).choose_spec

/-- Conjugating a `K`-automorphism of `L₂` to `L₁` and back returns it. -/
theorem conjHom_symm_conjHom {K L₁ L₂ : Type} [Field K] [Field L₁] [Field L₂] [Algebra K L₁]
    [Algebra K L₂] (e : L₁ ≃ₐ[K] L₂) (σ : Gal(L₂/K)) :
    NK.CFTLib.ARL.conjHom e (NK.CFTLib.ARL.conjHom e.symm σ) = σ := by
  ext x
  rw [NK.CFTLib.ARL.conjHom_apply, NK.CFTLib.ARL.conjHom_apply]
  simp [AlgEquiv.trans_apply]

/-- **The chosen Frobenius transports along a `K`-algebra isomorphism.** -/
theorem frobAtPrime_conjHom {K L₁ L₂ : Type} [Field K] [NumberField K] [Field L₁]
    [NumberField L₁] [Field L₂] [NumberField L₂] [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂] [IsGalois K L₁] [IsGalois K L₂]
    (e : L₁ ≃ₐ[K] L₂) (hc₁ : ∀ a b : Gal(L₁/K), a * b = b * a)
    (p : NK.Chebotarev.PrimeIdeal K)
    (hram : ∀ P : NK.Chebotarev.PrimeIdeal L₁, P.asIdeal.LiesOver p.asIdeal →
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    NK.Chebotarev.frobAtPrime (K := K) (L := L₂) p
      = NK.CFTLib.ARL.conjHom e (NK.Chebotarev.frobAtPrime (K := K) (L := L₁) p) := by
  obtain ⟨σ, -, huniq⟩ := NK.Chebotarev.ExistsUniqueIsFrobAtPrime hc₁ p hram
  have h2 : NK.CFTLib.ARL.conjHom e.symm (NK.Chebotarev.frobAtPrime (K := K) (L := L₂) p)
      = σ :=
    huniq _ ((NK.Chebotarev.IsFrobAtPrimeAlgEquivSameBase e.symm
      (NK.Chebotarev.frobAtPrime (K := K) (L := L₂) p) p).mp
        (isFrobAtPrime_frobAtPrime' (K := K) (L := L₂) p))
  have h3 : NK.Chebotarev.frobAtPrime (K := K) (L := L₁) p = σ :=
    huniq _ (isFrobAtPrime_frobAtPrime' (K := K) (L := L₁) p)
  rw [h3, ← h2, conjHom_symm_conjHom]

/-- **The Artin symbol of a fractional ideal transports along a `K`-algebra isomorphism**:
`ψ_{L₂/K}(A) = e ∘ ψ_{L₁/K}(A) ∘ e⁻¹` (conjugation by `e`). -/
theorem artinSym_algEquiv {K L₁ L₂ : Type} [Field K] [NumberField K] [Field L₁]
    [NumberField L₁] [Field L₂] [NumberField L₂] [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂] [IsGalois K L₁] [IsGalois K L₂]
    (e : L₁ ≃ₐ[K] L₂) (hc₁ : ∀ a b : Gal(L₁/K), a * b = b * a)
    (hc₂ : ∀ a b : Gal(L₂/K), a * b = b * a)
    (m : ℕ)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L₁) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal)
    (A : FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) (hA : A ≠ 0)
    (hcop : ∀ p : NK.Chebotarev.PrimeIdeal K,
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal →
      FractionalIdeal.count K p A = 0) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L₂) hc₂ A
      = NK.CFTLib.ARL.conjHom e (NK.CFTLib.Arl.artinSym (K := K) (L := L₁) hc₁ A) := by
  classical
  letI : CommMonoid Gal(L₁/K) := NK.CFTLib.Arl.galCommMonoid hc₁
  letI : CommMonoid Gal(L₂/K) := NK.CFTLib.Arl.galCommMonoid hc₂
  letI : IsMulCommutative Gal(L₁/K) := ⟨⟨hc₁⟩⟩
  letI : IsMulCommutative Gal(L₂/K) := ⟨⟨hc₂⟩⟩
  -- the support of `A` and the multiplicity function
  have hsmem : ∀ p : NK.Chebotarev.PrimeIdeal K,
      p ∈ (NK.CFTLib.Arl.exps A).support ↔ NK.CFTLib.Arl.exps A p ≠ 0 :=
    fun p => Finsupp.mem_support_iff
  have hfac : A = ((∏ p ∈ (NK.CFTLib.Arl.exps A).support,
      NK.CFTLib.ARL.primeUnit p ^ (NK.CFTLib.Arl.exps A p) :
        NK.CFTLib.ArtinReciprocityIdeal.Frac K) :
          FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) := by
    rw [Units.coe_prod]
    simp only [NK.CFTLib.ARL.primeUnit_val, Units.val_zpow_eq_zpow_val]
    rw [show (∏ p ∈ (NK.CFTLib.Arl.exps A).support,
        ((p.asIdeal : Ideal (NumberField.RingOfIntegers K)) :
          FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ^ (NK.CFTLib.Arl.exps A p))
        = ∏ᶠ (p : NK.Chebotarev.PrimeIdeal K),
            ((p.asIdeal : Ideal (NumberField.RingOfIntegers K)) :
              FractionalIdeal (NumberField.RingOfIntegers K)⁰ K) ^ (NK.CFTLib.Arl.exps A p) from
      (finprod_eq_prod_of_mulSupport_subset _ (by
        intro p hp
        exact Finsupp.mem_support_iff.mpr (fun h0 => hp (by simp [h0])))).symm]
    exact (FractionalIdeal.finprod_heightOneSpectrum_factorization' K hA).symm
  have hle : ∀ p ∈ (NK.CFTLib.Arl.exps A).support,
      (m : NumberField.RingOfIntegers K) ∉ p.asIdeal := fun p hp hmem =>
    (hsmem p).mp hp (hcop p hmem)
  -- the Frobenius transport at the primes of the support
  have key : ∀ p : NK.Chebotarev.PrimeIdeal K,
      (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      NK.Chebotarev.frobAtPrime (K := K) (L := L₂) p
        = NK.CFTLib.ARL.conjHom e (NK.Chebotarev.frobAtPrime (K := K) (L := L₁) p) := by
    intro p hpm
    exact frobAtPrime_conjHom e hc₁ p (fun P hP => by
      by_contra hne
      exact hpm (hram p fun h => hne (h P hP)))
  have hprime₁ : ∀ p : NK.Chebotarev.PrimeIdeal K,
      NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₁) hc₁
          (NK.CFTLib.ARL.primeUnit p : NK.CFTLib.ArtinReciprocityIdeal.Frac K)
        = NK.Chebotarev.frobAtPrime (K := K) (L := L₁) p := by
    intro p
    rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
      NK.CFTLib.ARL.primeUnit_val]
    exact NK.CFTLib.Arl.artinSym_prime (K := K) (L := L₁) hc₁ p
  have hprime₂ : ∀ p : NK.Chebotarev.PrimeIdeal K,
      NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₂) hc₂
          (NK.CFTLib.ARL.primeUnit p : NK.CFTLib.ArtinReciprocityIdeal.Frac K)
        = NK.Chebotarev.frobAtPrime (K := K) (L := L₂) p := by
    intro p
    rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
      NK.CFTLib.ARL.primeUnit_val]
    exact NK.CFTLib.Arl.artinSym_prime (K := K) (L := L₂) hc₂ p
  have hstep : ∀ p ∈ (NK.CFTLib.Arl.exps A).support,
      NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₂) hc₂
          ((NK.CFTLib.ARL.primeUnit p : NK.CFTLib.ArtinReciprocityIdeal.Frac K) ^
            (NK.CFTLib.Arl.exps A p))
        = NK.CFTLib.ARL.conjHom e
            (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₁) hc₁
              ((NK.CFTLib.ARL.primeUnit p : NK.CFTLib.ArtinReciprocityIdeal.Frac K) ^
                (NK.CFTLib.Arl.exps A p))) := by
    intro p hp
    rw [map_zpow, map_zpow, hprime₂ p, hprime₁ p, key p (hle p hp), map_zpow]
  rw [hfac]
  rw [← NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply (K := K) (L := L₂) hc₂
        (∏ p ∈ (NK.CFTLib.Arl.exps A).support,
          (NK.CFTLib.ARL.primeUnit p) ^ (NK.CFTLib.Arl.exps A p)),
    ← NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply (K := K) (L := L₁) hc₁
        (∏ p ∈ (NK.CFTLib.Arl.exps A).support,
          (NK.CFTLib.ARL.primeUnit p) ^ (NK.CFTLib.Arl.exps A p))]
  calc NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₂) hc₂
        (∏ p ∈ (NK.CFTLib.Arl.exps A).support,
          (NK.CFTLib.ARL.primeUnit p) ^ (NK.CFTLib.Arl.exps A p))
      = ∏ p ∈ (NK.CFTLib.Arl.exps A).support,
          NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₂) hc₂
            ((NK.CFTLib.ARL.primeUnit p) ^ (NK.CFTLib.Arl.exps A p)) :=
        map_prod (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₂) hc₂) _ _
    _ = ∏ p ∈ (NK.CFTLib.Arl.exps A).support,
          NK.CFTLib.ARL.conjHom e
            (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₁) hc₁
              ((NK.CFTLib.ARL.primeUnit p) ^ (NK.CFTLib.Arl.exps A p))) :=
        Finset.prod_congr rfl hstep
    _ = NK.CFTLib.ARL.conjHom e
          (∏ p ∈ (NK.CFTLib.Arl.exps A).support,
            NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₁) hc₁
              ((NK.CFTLib.ARL.primeUnit p) ^ (NK.CFTLib.Arl.exps A p))) :=
        (map_prod (NK.CFTLib.ARL.conjHom e) _ _).symm
    _ = NK.CFTLib.ARL.conjHom e
          (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₁) hc₁
            (∏ p ∈ (NK.CFTLib.Arl.exps A).support,
              (NK.CFTLib.ARL.primeUnit p) ^ (NK.CFTLib.Arl.exps A p))) :=
        (congrArg (NK.CFTLib.ARL.conjHom e)
          (map_prod (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₁) hc₁)
            _ _)).symm
    _ = NK.CFTLib.ARL.conjHom e (NK.CFTLib.Arl.artinSym (K := K) (L := L₁) hc₁
          ((∏ p ∈ (NK.CFTLib.Arl.exps A).support,
            (NK.CFTLib.ARL.primeUnit p) ^ (NK.CFTLib.Arl.exps A p) :
              NK.CFTLib.ArtinReciprocityIdeal.Frac K) :
            FractionalIdeal (NumberField.RingOfIntegers K)⁰ K)) := by
        rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply]


theorem finset_prod_zpow {ι G : Type*} [Group G] [IsMulCommutative G] (s : Finset ι) (g : G)
    (f : ι → ℤ) : ∏ i ∈ s, g ^ (f i) = g ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

/-! ## Two technical lemmas -/

/-- **A prime divisor of `M` divides the absolute norm of any prime ideal containing `M`.** -/
theorem exists_prime_dvd_absNorm_of_mem {K : Type} [Field K] [NumberField K]
    {M : ℕ} {𝔭 : NK.Chebotarev.PrimeIdeal K} (h : (M : 𝓞 K) ∈ 𝔭.asIdeal) :
    ∃ p : ℕ, p.Prime ∧ p ∣ M ∧ p ∣ Ideal.absNorm 𝔭.asIdeal := by
  classical
  set G : ℕ := Nat.gcd M (Ideal.absNorm 𝔭.asIdeal) with hG
  have hne : G ≠ 1 := by
    intro h1
    haveI : 𝔭.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime 𝔭.ne_bot 𝔭.isPrime
    letI : Field (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.Quotient.field 𝔭.asIdeal
    have hzero : ∀ z : ℕ, (z : 𝓞 K) ∈ 𝔭.asIdeal → (z : 𝓞 K ⧸ 𝔭.asIdeal) = 0 := by
      intro z hz
      rw [show ((z : 𝓞 K ⧸ 𝔭.asIdeal)) = Ideal.Quotient.mk 𝔭.asIdeal (z : 𝓞 K) from
        (map_natCast (Ideal.Quotient.mk 𝔭.asIdeal) z).symm]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
    have hM0 : (M : 𝓞 K ⧸ 𝔭.asIdeal) = 0 := hzero M h
    have hI0 : ((Ideal.absNorm 𝔭.asIdeal : ℕ) : 𝓞 K ⧸ 𝔭.asIdeal) = 0 :=
      hzero _ (Ideal.absNorm_mem 𝔭.asIdeal)
    have hbez : Nat.gcd M (Ideal.absNorm 𝔭.asIdeal)
        = M * Nat.gcdA M (Ideal.absNorm 𝔭.asIdeal)
          + Ideal.absNorm 𝔭.asIdeal * Nat.gcdB M (Ideal.absNorm 𝔭.asIdeal) :=
      Nat.gcd_eq_gcd_ab M _
    have hG0 : ((G : ℤ) : 𝓞 K ⧸ 𝔭.asIdeal) = 0 := by
      rw [hG, hbez]
      push_cast
      rw [hM0, hI0]
      ring
    have hG1 : ((G : ℤ) : 𝓞 K ⧸ 𝔭.asIdeal) = 1 := by
      rw [h1]; norm_num
    rw [hG0] at hG1
    exact one_ne_zero hG1.symm
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  exact ⟨p, hp, dvd_trans hpdvd (Nat.gcd_dvd_left _ _),
    dvd_trans hpdvd (Nat.gcd_dvd_right _ _)⟩

/-- **The product decomposition of a fractional ideal over its support.** -/
theorem frac_eq_prod_primeUnit {K : Type} [Field K] [NumberField K]
    (A : NK.CFTLib.ArtinReciprocityIdeal.Frac K) :
    A = ∏ 𝔭 ∈ (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)).support,
      (NK.CFTLib.ARL.primeUnit 𝔭) ^
        (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭 := by
  apply Units.ext
  rw [Units.coe_prod]
  simp only [NK.CFTLib.ARL.primeUnit_val, Units.val_zpow_eq_zpow_val]
  rw [show (∏ 𝔭 ∈ (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)).support,
      ((𝔭.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^
        (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭)
      = ∏ᶠ (𝔭 : NK.Chebotarev.PrimeIdeal K),
          ((𝔭.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^
            (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭 from
    (finprod_eq_prod_of_mulSupport_subset _ (by
      intro 𝔭 h𝔭
      exact Finsupp.mem_support_iff.mpr (fun h0 => h𝔭 (by simp [h0])))).symm]
  exact (FractionalIdeal.finprod_heightOneSpectrum_factorization' K (Units.ne_zero A)).symm



/-- **The relative norm of an ideal coprime to `(m)` is again coprime to `(m)`.** -/
theorem fracCoprime_relNormUnit {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] {m : ℕ} {A : NK.CFTLib.ArtinReciprocityIdeal.Frac L}
    (hA : NK.CFTLib.ArtinReciprocityIdeal.FracCoprime (K := L) m A) :
    NK.CFTLib.ArtinReciprocityIdeal.FracCoprime (K := K) m
      (NK.CFTLib.ARL.relNormUnit (K := K) (L := L) A) := by
  intro 𝔭 h𝔭
  rw [NK.CFTLib.ARL.relNormUnit_apply_e, NK.CFTLib.ARL.count_relNormFI,
    NK.CFTLib.ARL.relNormExp]
  refine Finset.sum_eq_zero fun 𝔔 h𝔔 => ?_
  have hlies : 𝔔.asIdeal.LiesOver 𝔭.asIdeal :=
    (NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := L)).mp h𝔔
  have hm𝔔 : (m : 𝓞 L) ∈ 𝔔.asIdeal := by
    have h1 := (Ideal.mem_under (𝓞 K) 𝔔.asIdeal).mp (hlies.over.symm ▸ h𝔭)
    simpa using h1
  rw [hA 𝔔 hm𝔔, mul_zero]

/-! ## The transfer: `ker ψ ∩ I(m) ⊆ P(m)·𝔑(m)` -/

theorem kernelLe_of_auxField (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    [IsMulCommutative (Gal(L/K))]
    (m : ℕ) (hm : 0 < m) (haux : NK.CFTLib.ARL.AuxFieldHyp K L m)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : NumberField.RingOfIntegers K) ∈ p.asIdeal) :
    ∀ A : NK.CFTLib.ArtinReciprocityIdeal.Frac K,
      NK.CFTLib.ArtinReciprocityIdeal.FracCoprime m A →
      NK.CFTLib.Arl.artinSym (K := K) (L := L)
        (fun a b : Gal(L/K) => IsMulCommutative.is_comm.comm a b) A = 1 →
      A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay K L m := by
  classical
  intro A hcop hsym
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  set Afr : FractionalIdeal (𝓞 K)⁰ K := (A : FractionalIdeal (𝓞 K)⁰ K) with hAfrdef
  set s : Finset (NK.Chebotarev.PrimeIdeal K) := (NK.CFTLib.Arl.exps Afr).support with hsdef
  have hfac : A = ∏ 𝔭 ∈ s, (NK.CFTLib.ARL.primeUnit 𝔭) ^ (NK.CFTLib.Arl.exps Afr) 𝔭 := by
    rw [hsdef]; exact frac_eq_prod_primeUnit A
  have hs : ∀ 𝔭 ∈ s, (m : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro 𝔭 h𝔭 hmem
    have hmem' : 𝔭 ∈ (NK.CFTLib.Arl.exps Afr).support := by rw [← hsdef]; exact h𝔭
    exact (Finsupp.mem_support_iff.mp hmem') (by
      rw [NK.CFTLib.Arl.exps_apply]; exact hcop 𝔭 hmem)
  rcases s.eq_empty_or_nonempty with hsemp | hsne
  · rw [hfac, hsemp, Finset.prod_empty]; exact Subgroup.one_mem _
  obtain ⟨𝔭₀, h𝔭₀⟩ := hsne
  -- ## the auxiliary data
  obtain ⟨M, hMne, hMcop, hMS, hMN, hdisjζ, E, hEdisj, hE𝔭⟩ := haux s hs ∅ (by simp)
  haveI hMneI : NeZero M := hMne
  set LΩ : IntermediateField K (CyclotomicField M L) :=
    NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M with hLΩdef
  set ζ : CyclotomicField M L := IsCyclotomicExtension.zeta M L (CyclotomicField M L) with hζdef
  haveI hgalΩ : IsGalois K (CyclotomicField M L) :=
    NK.CFTLib.ARL.isGalois_cyclotomicField_over_base (K := K) (L := L) M
  set 𝔪 : ℕ := m * M with h𝔪def
  have h𝔪pos : 0 < 𝔪 := Nat.mul_pos hm (NeZero.pos M)
  have hmlt : m ∣ 𝔪 := ⟨M, by rw [h𝔪def]⟩
  -- ## the auxiliary fields `E𝔭`
  have hE' : ∀ 𝔭 : {𝔭 : NK.Chebotarev.PrimeIdeal K // 𝔭 ∈ s},
      ∃ E𝔭 : IntermediateField K (CyclotomicField M L),
        E𝔭 ≤ E ∧ ((E𝔭.restrictScalars ℚ) ⊔ (IntermediateField.adjoin ℚ
          ({ζ} : Set (CyclotomicField M L))) = ⊤) ∧
        NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥E𝔭) 𝔭.1 1 :=
    fun 𝔭 => hE𝔭 𝔭.1 𝔭.2
  choose Ef hEfle hEfjoin hEfsplit using hE'
  -- ## cyclotomicity
  have hsupE : (E.restrictScalars ℚ) ⊔ (IntermediateField.adjoin ℚ
      ({ζ} : Set (CyclotomicField M L))) = ⊤ := by
    rw [eq_top_iff]
    refine le_trans (le_of_eq (hEfjoin ⟨𝔭₀, h𝔭₀⟩).symm) ?_
    exact sup_le_sup_right (fun x hx => hEfle ⟨𝔭₀, h𝔭₀⟩ hx) _
  haveI hcycE : IsCyclotomicExtension {M} ↥E (CyclotomicField M L) :=
    NK.CFTLib.ARLAlt.isCyclotomicExtension_of_sup_adjoin_zeta (K := K) (L := L) M E hsupE
  haveI habelE : IsAbelianGalois ↥E (CyclotomicField M L) :=
    IsCyclotomicExtension.isAbelianGalois {M} ↥E (CyclotomicField M L)
  haveI hcommCycE : IsMulCommutative (Gal(CyclotomicField M L/↥E)) :=
    habelE.toIsMulCommutative
  -- ## `LΩ` and its Galois theory
  haveI hcommΩ : IsMulCommutative (Gal(↥LΩ/K)) :=
    NK.CFTLib.ARL.isMulCommutative_LImage (K := K) (L := L) M
  have hcommΩ' : ∀ a b : Gal(↥LΩ/K), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  haveI hgalE : IsGalois K ↥E :=
    NK.CFTLib.ARL.isGalois_intermediateField_cyclotomicField_aux (K := K) (L := L) hcomm M E
  haveI hnfE : NumberField ↥E :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField E
  haveI hnfLΩ : NumberField ↥LΩ :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField LΩ
  -- ## the ramification hypotheses at the modulus `𝔪`
  have hunrE : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥E, (M : 𝓞 ↥E) ∉ 𝔮.asIdeal →
      NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E)
        (L := CyclotomicField M L) 𝔮 :=
    fun 𝔮 h𝔮 => NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (k := ↥E)
      (Ω := CyclotomicField M L) M 𝔮 h𝔮
  have hramE : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥E,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E)
        (L := CyclotomicField M L) 𝔮 → (𝔪 : 𝓞 ↥E) ∈ 𝔮.asIdeal := by
    intro 𝔮 h
    have hM : (M : 𝓞 ↥E) ∈ 𝔮.asIdeal := by
      by_contra hM
      exact h (hunrE 𝔮 hM)
    have h2 : ((m * M : ℕ) : 𝓞 ↥E) ∈ 𝔮.asIdeal := by
      rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ hM
    exact h2
  have hramL : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (𝔪 : 𝓞 K) ∈ p.asIdeal := by
    intro p hp
    have hm' : (m : 𝓞 K) ∈ p.asIdeal := hram p hp
    have h2 : ((m * M : ℕ) : 𝓞 K) ∈ p.asIdeal := by
      rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hm'
    exact h2
  have hramLΩ : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥LΩ) p →
      (𝔪 : 𝓞 K) ∈ p.asIdeal := by
    intro p hp
    have h2 : (m : 𝓞 K) ∈ p.asIdeal ∨ (M : 𝓞 K) ∈ p.asIdeal := by
      by_contra hc
      push_neg at hc
      exact hp (NK.CFTLib.ARL.isUnramified_LImage (K := K) (L := L) M m hram p hc.1 hc.2)
    have h3 : ((m * M : ℕ) : 𝓞 K) ∈ p.asIdeal := by
      rw [Nat.cast_mul]
      rcases h2 with h | h
      · exact Ideal.mul_mem_right _ _ h
      · exact Ideal.mul_mem_left _ _ h
    exact h3
  -- ## `A` is coprime to `(𝔪)`
  have hMnotmem : ∀ 𝔭 ∈ s, (M : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro 𝔭 h𝔭 hmem
    obtain ⟨p, hp, hpM, hpN⟩ := exists_prime_dvd_absNorm_of_mem (K := K) hmem
    exact hMN p hp hpM 𝔭 h𝔭 hpN
  have hcop𝔪 : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K, (𝔪 : 𝓞 K) ∈ 𝔭.asIdeal →
      FractionalIdeal.count K 𝔭 Afr = 0 := by
    intro 𝔭 hmem
    have hmem' : (m : 𝓞 K) ∈ 𝔭.asIdeal ∨ (M : 𝓞 K) ∈ 𝔭.asIdeal := by
      have h2 := hmem
      rw [h𝔪def, Nat.cast_mul] at h2
      exact Ideal.IsPrime.mem_or_mem 𝔭.isPrime h2
    rcases hmem' with h | h
    · exact hcop 𝔭 h
    · by_contra hne
      exact hMnotmem 𝔭 (by rw [hsdef]; exact Finsupp.mem_support_iff.mpr hne) h
  -- ## the transport to `LΩ`
  have hsym' : NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm Afr = 1 := hsym
  have hsymΩ : NK.CFTLib.Arl.artinSym (K := K) (L := ↥LΩ) hcommΩ' Afr = 1 := by
    have h := artinSym_algEquiv (K := K) (L₁ := L) (L₂ := ↥LΩ)
      (NK.CFTLib.ARLAlt.LImageEquiv (K := K) (L := L) M).symm hcomm hcommΩ' 𝔪 hramL
      Afr (Units.ne_zero A) hcop𝔪
    rw [h, hsym', map_one]
  -- ## the generator of `Gal(LΩ/K)` and the exponents
  haveI hcycΩ : IsCyclic (Gal(↥LΩ/K)) :=
    (MulEquiv.isCyclic (AlgEquiv.autCongr
      (NK.CFTLib.ARLAlt.LImageEquiv (K := K) (L := L) M).symm)).mp
      (inferInstance : IsCyclic (Gal(L/K)))
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(↥LΩ/K))
  have hexpS : ∀ 𝔮 ∈ s, ∃ t : ℤ, NK.Chebotarev.frobAtPrime (K := K) (L := ↥LΩ) 𝔮 = σ ^ t :=
    fun 𝔮 _ => by
      obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp (hσ _)
      exact ⟨t, ht.symm⟩
  let sEx : NK.Chebotarev.PrimeIdeal K → ℤ := fun 𝔮 =>
    if h : 𝔮 ∈ s then Classical.choose (hexpS 𝔮 h) else 0
  have hsEx : ∀ 𝔮 ∈ s, NK.Chebotarev.frobAtPrime (K := K) (L := ↥LΩ) 𝔮 = σ ^ (sEx 𝔮) := by
    intro 𝔮 h𝔮
    simp only [sEx, dif_pos h𝔮]
    exact Classical.choose_spec (hexpS 𝔮 h𝔮)
  -- ## the exponent `N` of `𝔟`
  set N : ℤ := ∑ 𝔮 ∈ s, (NK.CFTLib.Arl.exps Afr) 𝔮 * sEx 𝔮 with hNdef
  have hσN : σ ^ N = 1 := by
    have hFfac : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥LΩ) hcommΩ' A
        = ∏ 𝔮 ∈ s, NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥LΩ)
            hcommΩ' ((NK.CFTLib.ARL.primeUnit 𝔮) ^ (NK.CFTLib.Arl.exps Afr) 𝔮) := by
      rw [hfac]; exact map_prod _ _ s
    have hprime : ∀ 𝔮 ∈ s, NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K)
        (L := ↥LΩ) hcommΩ' (NK.CFTLib.ARL.primeUnit 𝔮)
          = NK.Chebotarev.frobAtPrime (K := K) (L := ↥LΩ) 𝔮 := by
      intro 𝔮 _
      rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
        NK.CFTLib.ARL.primeUnit_val]
      exact NK.CFTLib.Arl.artinSym_prime (K := K) (L := ↥LΩ) hcommΩ' 𝔮
    have hmain : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥LΩ) hcommΩ' A
        = σ ^ N := by
      rw [hFfac, hNdef]
      rw [show (∑ 𝔮 ∈ s, (NK.CFTLib.Arl.exps Afr) 𝔮 * sEx 𝔮)
          = ∑ 𝔮 ∈ s, sEx 𝔮 * (NK.CFTLib.Arl.exps Afr) 𝔮 from
        Finset.sum_congr rfl fun 𝔮 _ => mul_comm _ _]
      have : ∀ 𝔮 ∈ s, NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥LΩ)
          hcommΩ' ((NK.CFTLib.ARL.primeUnit 𝔮) ^ (NK.CFTLib.Arl.exps Afr) 𝔮)
            = σ ^ (sEx 𝔮 * (NK.CFTLib.Arl.exps Afr) 𝔮) := by
        intro 𝔮 h𝔮
        rw [map_zpow, hprime 𝔮 h𝔮, hsEx 𝔮 h𝔮, zpow_mul]
      rw [Finset.prod_congr rfl this]
      exact finset_prod_zpow s σ (fun 𝔮 => sEx 𝔮 * (NK.CFTLib.Arl.exps Afr) 𝔮)
    rw [← hmain, NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply]
    exact hsymΩ
  -- ## `n = [L:K]` divides `N`
  have hcard : Nat.card (Gal(↥LΩ/K)) = Module.finrank K L := by
    rw [IsGalois.card_aut_eq_finrank K ↥LΩ]
    exact (AlgEquiv.toLinearEquiv (NK.CFTLib.ARLAlt.LImageEquiv (K := K) (L := L) M)).finrank_eq
  have horder : orderOf σ = Module.finrank K L := by
    rw [← hcard]
    exact orderOf_eq_card_of_forall_mem_zpowers hσ
  have hdvd : (Module.finrank K L : ℤ) ∣ N := by
    rw [← horder]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hσN
  -- ## the auxiliary ideal `𝔅` over `E` and `𝔟 = N_{E/K}(𝔅)`
  have hdisj : E ⊓ LΩ = ⊥ := disjoint_iff.mp hEdisj
  obtain ⟨τ, hτ⟩ := NK.CFTLib.ARL.restrictNormalHom_comp_restrictScalars_surjective
    (K := K) (Ω := CyclotomicField M L) E LΩ hdisj σ
  obtain ⟨𝔅, h𝔅⟩ := NK.CFTLib.ArtinReciprocityIdeal.artinSymSurjectiveOnCoprime
    (K := ↥E) (L := CyclotomicField M L) 𝔪 h𝔪pos hramE τ
  have hcop𝔅 : NK.CFTLib.ArtinReciprocityIdeal.FracCoprime (K := ↥E) 𝔪
      (𝔅 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E) :=
    (NK.CFTLib.ArtinReciprocityIdeal.mem_idealCoprimeGroup_iff (K := ↥E) 𝔪 _).mp 𝔅.2
  set 𝔟 : NK.CFTLib.ArtinReciprocityIdeal.Frac K :=
    NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥E)
      (𝔅 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E) with h𝔟def
  have h𝔟sym : NK.CFTLib.Arl.artinSym (K := K) (L := ↥LΩ) hcommΩ'
      (𝔟 : FractionalIdeal (𝓞 K)⁰ K) = σ := by
    have h := NK.CFTLib.ARL.artinSym_restrict_relNorm' (K := K) (M := CyclotomicField M L)
      E LΩ (fun a b : Gal(CyclotomicField M L/↥E) => IsMulCommutative.is_comm.comm a b)
      hcommΩ' 𝔪 hramE hramLΩ (𝔅 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E) hcop𝔅
    rw [h𝔅] at h
    have h2 : (AlgEquiv.restrictNormalHom (F := K) (K₁ := CyclotomicField M L) ↥LΩ)
        (AlgEquiv.restrictScalars K τ) = σ := hτ
    rw [h2] at h
    exact h.symm
  have hcop𝔟 : NK.CFTLib.ArtinReciprocityIdeal.FracCoprime 𝔪 𝔟 :=
    fracCoprime_relNormUnit (K := K) (L := ↥E) hcop𝔅
  -- ## the per-prime elements `X 𝔭`
  set Xa : NK.Chebotarev.PrimeIdeal K → NK.CFTLib.ArtinReciprocityIdeal.Frac K := fun 𝔭 =>
    (NK.CFTLib.ARL.primeUnit 𝔭) ^ (NK.CFTLib.Arl.exps Afr) 𝔭 *
      𝔟 ^ (-((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭)) with hXadef
  have hXmem : ∀ 𝔭 ∈ s, Xa 𝔭 ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
      NK.CFTLib.ArtinReciprocityIdeal.normRay K ↥LΩ m := by
    intro 𝔭 h𝔭
    -- the auxiliary field at `𝔭`
    have hsup𝔭 : ((Ef ⟨𝔭, h𝔭⟩).restrictScalars ℚ) ⊔ (IntermediateField.adjoin ℚ
        ({ζ} : Set (CyclotomicField M L))) = ⊤ := hEfjoin ⟨𝔭, h𝔭⟩
    have hle𝔭 : Ef ⟨𝔭, h𝔭⟩ ≤ E := hEfle ⟨𝔭, h𝔭⟩
    haveI hcyc𝔭 : IsCyclotomicExtension {M} ↥(Ef ⟨𝔭, h𝔭⟩) (CyclotomicField M L) :=
      NK.CFTLib.ARLAlt.isCyclotomicExtension_of_sup_adjoin_zeta (K := K) (L := L) M
        (Ef ⟨𝔭, h𝔭⟩) hsup𝔭
    haveI habel𝔭 : IsAbelianGalois ↥(Ef ⟨𝔭, h𝔭⟩) (CyclotomicField M L) :=
      IsCyclotomicExtension.isAbelianGalois {M} ↥(Ef ⟨𝔭, h𝔭⟩) (CyclotomicField M L)
    haveI hcomm𝔭 : IsMulCommutative (Gal(CyclotomicField M L/↥(Ef ⟨𝔭, h𝔭⟩))) :=
      habel𝔭.toIsMulCommutative
    have hcomm𝔭' : ∀ a b : Gal(CyclotomicField M L/↥(Ef ⟨𝔭, h𝔭⟩)), a * b = b * a :=
      fun a b => IsMulCommutative.is_comm.comm a b
    haveI hmcCell : IsMulCommutative (Gal(↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩)
        (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left)/↥(Ef ⟨𝔭, h𝔭⟩))) :=
      NK.CFTLib.ARLAlt.isMulCommutative_ofLe_sup (K := K) (L := L) M (Ef ⟨𝔭, h𝔭⟩) hsup𝔭
    have hcommCell' : ∀ a b : Gal(↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩)
        (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left)/↥(Ef ⟨𝔭, h𝔭⟩)), a * b = b * a :=
      fun a b => IsMulCommutative.is_comm.comm a b
    -- the prime `𝔓 | 𝔭` with trivial Frobenius
    obtain ⟨𝔓, h𝔓lies, h𝔓frob, h𝔓norm⟩ :=
      NK.CFTLib.ARLAlt.exists_primeIdeal_isFrobAt_one (Ef ⟨𝔭, h𝔭⟩) 𝔭 (hEfsplit ⟨𝔭, h𝔭⟩)
    -- the ramification hypotheses
    have hram𝔭 : ∀ q : NK.Chebotarev.PrimeIdeal ↥(Ef ⟨𝔭, h𝔭⟩),
        ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥(Ef ⟨𝔭, h𝔭⟩))
          (L := CyclotomicField M L) q → (𝔪 : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩)) ∈ q.asIdeal := by
      intro q hq
      have hM : (M : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩)) ∈ q.asIdeal := by
        by_contra hM
        exact hq (NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (k := ↥(Ef ⟨𝔭, h𝔭⟩))
          (Ω := CyclotomicField M L) M q hM)
      have h2 : ((m * M : ℕ) : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩)) ∈ q.asIdeal := by
        rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ hM
      exact h2
    have hcellunr : ∀ q : NK.Chebotarev.PrimeIdeal ↥(Ef ⟨𝔭, h𝔭⟩),
        ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥(Ef ⟨𝔭, h𝔭⟩))
          (L := ↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩) (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left)) q →
        (𝔪 : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩)) ∈ q.asIdeal := by
      intro q hq
      have hM : (M : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩)) ∈ q.asIdeal := by
        by_contra hM
        exact hq (NK.CFTLib.ARL.isUnramified_cellAtAux (K := K) (L := L) M (Ef ⟨𝔭, h𝔭⟩)
          hsup𝔭 q hM)
      have h2 : ((m * M : ℕ) : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩)) ∈ q.asIdeal := by
        rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ hM
      exact h2
    -- the norm `𝔠` and the ideal `𝔘`
    letI : Algebra ↥(Ef ⟨𝔭, h𝔭⟩) ↥E := NK.CFTLib.ARL.algOfLe (Ef ⟨𝔭, h𝔭⟩) E hle𝔭
    letI : IsScalarTower K ↥(Ef ⟨𝔭, h𝔭⟩) ↥E :=
      NK.CFTLib.ARL.isScalarTower_algOfLe (Ef ⟨𝔭, h𝔭⟩) E hle𝔭
    letI : FiniteDimensional ↥(Ef ⟨𝔭, h𝔭⟩) ↥E :=
      NK.CFTLib.ARL.finiteDimensional_algOfLe (Ef ⟨𝔭, h𝔭⟩) E hle𝔭
    set 𝔠 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥(Ef ⟨𝔭, h𝔭⟩) :=
      NK.CFTLib.ARL.relNormUnit (K := ↥(Ef ⟨𝔭, h𝔭⟩)) (L := ↥E)
        (𝔅 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E) with h𝔠def
    set 𝔘 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥(Ef ⟨𝔭, h𝔭⟩) :=
      (NK.CFTLib.ARL.primeUnit 𝔓) ^ (NK.CFTLib.Arl.exps Afr) 𝔭 *
        𝔠 ^ (-((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭)) with h𝔘def
    -- `𝔘` is coprime to `(𝔪)`
    have h𝔪𝔓 : (𝔪 : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩)) ∉ 𝔓.asIdeal := by
      intro h
      have h2 : (𝔪 : 𝓞 K) ∈ 𝔓.asIdeal.under (𝓞 K) :=
        (Ideal.mem_under (𝓞 K) 𝔓.asIdeal).mpr (by simpa using h)
      rw [← h𝔓lies.over] at h2
      rw [h𝔪def, Nat.cast_mul] at h2
      rcases Ideal.IsPrime.mem_or_mem 𝔭.isPrime h2 with h3 | h3
      · exact hs 𝔭 h𝔭 h3
      · exact hMnotmem 𝔭 h𝔭 h3
    have hcop𝔠 : NK.CFTLib.ArtinReciprocityIdeal.FracCoprime (K := ↥(Ef ⟨𝔭, h𝔭⟩)) 𝔪 𝔠 :=
      fracCoprime_relNormUnit (K := ↥(Ef ⟨𝔭, h𝔭⟩)) (L := ↥E) hcop𝔅
    have h𝔘mem : 𝔘 ∈ NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroup (↥(Ef ⟨𝔭, h𝔭⟩)) 𝔪 := by
      rw [h𝔘def]
      refine Subgroup.mul_mem _ (Subgroup.zpow_mem _ ?_ _) (Subgroup.zpow_mem _ ?_ _)
      · exact Subgroup.subset_closure ⟨𝔓, h𝔪𝔓, rfl⟩
      · exact (NK.CFTLib.ArtinReciprocityIdeal.mem_idealCoprimeGroup_iff
          (K := ↥(Ef ⟨𝔭, h𝔭⟩)) 𝔪 𝔠).mpr hcop𝔠
    have hcop𝔘 : NK.CFTLib.ArtinReciprocityIdeal.FracCoprime (K := ↥(Ef ⟨𝔭, h𝔭⟩)) 𝔪 𝔘 :=
      (NK.CFTLib.ArtinReciprocityIdeal.mem_idealCoprimeGroup_iff
        (K := ↥(Ef ⟨𝔭, h𝔭⟩)) 𝔪 𝔘).mp h𝔘mem
    -- `N_{E𝔭/K}𝔘 = X 𝔭`
    have hN𝔘 : NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef ⟨𝔭, h𝔭⟩)) 𝔘 = Xa 𝔭 := by
      simp only [hXadef]
      rw [h𝔘def, h𝔠def, h𝔟def]
      have h1 : NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef ⟨𝔭, h𝔭⟩))
          (NK.CFTLib.ARL.primeUnit 𝔓) = NK.CFTLib.ARL.primeUnit 𝔭 := by
        refine Units.ext ?_
        rw [NK.CFTLib.ARL.relNormUnit_primeUnit, NK.CFTLib.ARL.primeUnit_val,
          Units.val_mk0, h𝔓norm]
      have h2 : NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef ⟨𝔭, h𝔭⟩))
          (NK.CFTLib.ARL.relNormUnit (K := ↥(Ef ⟨𝔭, h𝔭⟩)) (L := ↥E)
            (𝔅 : (FractionalIdeal (𝓞 ↥E)⁰ ↥E)ˣ))
          = NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥E)
            (𝔅 : (FractionalIdeal (𝓞 ↥E)⁰ ↥E)ˣ) :=
        NK.CFTLib.ARL.relNormUnit_trans (K := K) (E := ↥(Ef ⟨𝔭, h𝔭⟩)) (M := ↥E) _
      rw [map_mul, map_zpow, map_zpow, h1, h2]
    -- `ψ_{LΩ/K}(X 𝔭) = 1`
    have hXsym : NK.CFTLib.Arl.artinSym (K := K) (L := ↥LΩ) hcommΩ'
        (Xa 𝔭 : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
      have h1 : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥LΩ) hcommΩ'
          (Xa 𝔭) = 1 := by
        simp only [hXadef]
        rw [map_mul, map_zpow, map_zpow,
          NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
          NK.CFTLib.ARL.primeUnit_val,
          NK.CFTLib.Arl.artinSym_prime (K := K) (L := ↥LΩ) hcommΩ' 𝔭,
          hsEx 𝔭 h𝔭,
          NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply, h𝔟sym]
        rw [← zpow_mul, ← zpow_add,
          show sEx 𝔭 * (NK.CFTLib.Arl.exps Afr) 𝔭 +
            -((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭) = 0 from by ring, zpow_zero]
      rw [← NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply (K := K) (L := ↥LΩ) hcommΩ'
        (Xa 𝔭)]
      exact h1
    -- the restriction to `LΩ` of the Artin symbol of `𝔘` is trivial
    have hρ : NK.CFTLib.Arl.restrictGalEquiv (Ef ⟨𝔭, h𝔭⟩) LΩ
        (NK.CFTLib.Arl.artinSym (K := ↥(Ef ⟨𝔭, h𝔭⟩)) (L := CyclotomicField M L) hcomm𝔭'
          (𝔘 : FractionalIdeal (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))⁰ ↥(Ef ⟨𝔭, h𝔭⟩))) = 1 := by
      have h := NK.CFTLib.ARL.artinSym_restrict_relNorm' (K := K) (M := CyclotomicField M L)
        (Ef ⟨𝔭, h𝔭⟩) LΩ hcomm𝔭' hcommΩ' 𝔪 hram𝔭 hramLΩ
        (𝔘 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥(Ef ⟨𝔭, h𝔭⟩)) hcop𝔘
      change (AlgEquiv.restrictNormalHom (F := K) (K₁ := CyclotomicField M L) ↥LΩ)
        (AlgEquiv.restrictScalars K (NK.CFTLib.Arl.artinSym (K := ↥(Ef ⟨𝔭, h𝔭⟩))
          (L := CyclotomicField M L) hcomm𝔭'
          (𝔘 : FractionalIdeal (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))⁰ ↥(Ef ⟨𝔭, h𝔭⟩)))) = 1
      rw [h]
      rw [show NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef ⟨𝔭, h𝔭⟩)) 𝔘 = Xa 𝔭 from hN𝔘]
      exact hXsym
    -- hence the Artin symbol of `𝔘` in `LE𝔭/E𝔭` is trivial
    have hψ : NK.CFTLib.Arl.artinSym (K := ↥(Ef ⟨𝔭, h𝔭⟩))
        (L := ↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩) (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left))
        hcommCell' (𝔘 : FractionalIdeal (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))⁰ ↥(Ef ⟨𝔭, h𝔭⟩)) = 1 := by
      rw [← NK.CFTLib.ARL.artinSym_restrictNormalHom
        (T := NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩) (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left)
        hcomm𝔭' hcommCell' 𝔪 hram𝔭 (𝔘 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥(Ef ⟨𝔭, h𝔭⟩))
        hcop𝔘]
      let σ' : CyclotomicField M L ≃ₐ[K] CyclotomicField M L := AlgEquiv.restrictScalars K
        (NK.CFTLib.Arl.artinSym (K := ↥(Ef ⟨𝔭, h𝔭⟩)) (L := CyclotomicField M L) hcomm𝔭'
          (𝔘 : FractionalIdeal (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))⁰ ↥(Ef ⟨𝔭, h𝔭⟩)))
      have hFixF : Ef ⟨𝔭, h𝔭⟩ ≤ IntermediateField.fixedField (Subgroup.zpowers σ') := by
        rw [IntermediateField.le_iff_le, Subgroup.zpowers_le,
          IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        show σ' x = x
        exact AlgEquiv.commutes (NK.CFTLib.Arl.artinSym (K := ↥(Ef ⟨𝔭, h𝔭⟩))
          (L := CyclotomicField M L) hcomm𝔭'
          (𝔘 : FractionalIdeal (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))⁰ ↥(Ef ⟨𝔭, h𝔭⟩))) ⟨x, hx⟩
      have hFixL : LΩ ≤ IntermediateField.fixedField (Subgroup.zpowers σ') := by
        rw [IntermediateField.le_iff_le, Subgroup.zpowers_le,
          IntermediateField.mem_fixingSubgroup_iff]
        intro y hy
        have h2 := congrArg (fun τ : ↥LΩ ≃ₐ[K] ↥LΩ => (τ ⟨y, hy⟩ : CyclotomicField M L)) hρ
        simpa only [NK.CFTLib.Arl.restrictGalEquiv_apply, AlgEquiv.restrictNormalHom_apply,
          AlgEquiv.one_apply, σ'] using h2
      refine AlgEquiv.ext (fun x => Subtype.ext ?_)
      rw [AlgEquiv.restrictNormalHom_apply]
      have hxmem : (x : CyclotomicField M L) ∈
          IntermediateField.fixedField (Subgroup.zpowers σ') := sup_le hFixF hFixL x.2
      rw [IntermediateField.mem_fixedField_iff] at hxmem
      exact hxmem σ' (Subgroup.mem_zpowers σ')
    -- the cell
    have hcell : 𝔘 ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay ↥(Ef ⟨𝔭, h𝔭⟩) 𝔪 ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRay ↥(Ef ⟨𝔭, h𝔭⟩)
          ↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩) (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left) 𝔪 :=
      NK.CFTLib.ARLAlt.cellAtAuxField (K := K) (L := L) M (Ef ⟨𝔭, h𝔭⟩) hsup𝔭 𝔪 h𝔪pos
        ⟨m, by rw [h𝔪def, mul_comm]⟩ hcellunr 𝔘 hcop𝔘 hψ
    -- descent to `K`
    have hPR := NK.CFTLib.ARLAlt.principalRay_map_relNormUnit_le (K := K) (E := ↥(Ef ⟨𝔭, h𝔭⟩))
      𝔪 m hm h𝔪pos hmlt
    letI : Algebra ↥LΩ ↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩) (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left) :=
      inferInstanceAs (Algebra ↥LΩ ↥(NK.CFTLib.ARLAlt.ofLe LΩ (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_right))
    letI : IsScalarTower K ↥LΩ
        ↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩) (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left) :=
      inferInstanceAs (IsScalarTower K ↥LΩ
        ↥(NK.CFTLib.ARLAlt.ofLe LΩ (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_right))
    have hNR := NK.CFTLib.ARLAlt.normRay_map_relNormUnit_le (K := K) (L := ↥LΩ)
      (E := ↥(Ef ⟨𝔭, h𝔭⟩))
      (LE := ↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩) (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left))
      𝔪 m hm hmlt
    have : NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef ⟨𝔭, h𝔭⟩)) 𝔘 ∈
        NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay K ↥LΩ m := by
      rcases Subgroup.mem_sup.mp hcell with ⟨a, ha, b, hb, hab⟩
      have hmap := Subgroup.mem_map_of_mem
        (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef ⟨𝔭, h𝔭⟩))) hcell
      rw [Subgroup.map_sup] at hmap
      have h1 : (NK.CFTLib.ArtinReciprocityIdeal.principalRay ↥(Ef ⟨𝔭, h𝔭⟩) 𝔪).map
            (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef ⟨𝔭, h𝔭⟩))) ⊔
          (NK.CFTLib.ArtinReciprocityIdeal.normRay ↥(Ef ⟨𝔭, h𝔭⟩)
            ↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩) (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left) 𝔪).map
            (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef ⟨𝔭, h𝔭⟩))) ≤
          NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
            NK.CFTLib.ArtinReciprocityIdeal.normRay K ↥LΩ m :=
        sup_le (hPR.trans le_sup_left) (hNR.trans le_sup_right)
      exact h1 hmap
    rw [← hN𝔘]
    exact this
  -- ## bookkeeping
  have hXprod : ∏ 𝔭 ∈ s, Xa 𝔭 = A * 𝔟 ^ (-N) := by
    simp only [hXadef]
    rw [Finset.prod_mul_distrib, hfac]
    rw [finset_prod_zpow, Finset.sum_neg_distrib, ← hNdef]
  have hprodmem : ∏ 𝔭 ∈ s, Xa 𝔭 ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
      NK.CFTLib.ArtinReciprocityIdeal.normRay K ↥LΩ m :=
    Subgroup.prod_mem _ (fun 𝔭 h𝔭 => hXmem 𝔭 h𝔭)
  have hcop𝔟m : NK.CFTLib.ArtinReciprocityIdeal.FracCoprime m 𝔟 := fun 𝔭 hmem =>
    hcop𝔟 𝔭 (by rw [h𝔪def, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hmem)
  have hfin : Module.finrank K ↥LΩ = Module.finrank K L := by
    rw [← IsGalois.card_aut_eq_finrank K ↥LΩ, hcard]
  have hbase : 𝔟 ^ Module.finrank K L ∈ NK.CFTLib.ArtinReciprocityIdeal.normRay K ↥LΩ m := by
    have h := NK.Existence.ArtinLemma.pow_finrank_mem_normRay (K := K) (L := ↥LΩ) m hcop𝔟m
    rwa [hfin] at h
  obtain ⟨k, hk⟩ := hdvd
  have h𝔟N : 𝔟 ^ N ∈ NK.CFTLib.ArtinReciprocityIdeal.normRay K ↥LΩ m := by
    rw [hk, zpow_mul, zpow_natCast]
    exact Subgroup.zpow_mem _ hbase k
  have hfinal : A ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
      NK.CFTLib.ArtinReciprocityIdeal.normRay K ↥LΩ m := by
    have hAeq : A = (∏ 𝔭 ∈ s, Xa 𝔭) * 𝔟 ^ N := by
      rw [hXprod]; group
    rw [hAeq]
    exact Subgroup.mul_mem _ hprodmem (Subgroup.mem_sup_right h𝔟N)
  have hle : NK.CFTLib.ArtinReciprocityIdeal.normRay K ↥LΩ m ≤
      NK.CFTLib.ArtinReciprocityIdeal.normRay K L m :=
    NK.CFTLib.ARL.normRay_le_of_algEquiv
      (NK.CFTLib.ARLAlt.LImageEquiv (K := K) (L := L) M).symm m
  exact (sup_le le_sup_left (hle.trans le_sup_right)) hfinal

end

end NK.NUV2.ChebAux
