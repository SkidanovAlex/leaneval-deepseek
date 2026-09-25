import Mathlib
import Submission.NK.CFTLib.ARL.AuxField
import Submission.NK.CFTLib.ArtinReciprocityIdeal.cyclotomicKernelLe
import Submission.NK.CFTLib.ArtinReciprocityIdeal.normRayLeKer
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSymSurjectiveOnCoprime
import Submission.NK.CFTLib.ArtinReciprocityIdeal.LangDefs
import Submission.NK.CFTLib.ArtinReciprocityIdeal.relNormUnit_trans
import Submission.NK.CFTLib.ArtinReciprocityIdeal.norm_principalRay_le
import Submission.NK.CFTLib.ArtinReciprocityIdeal.mem_idealCoprimeGroup_iff
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSym_restrict_relNorm
import Submission.NK.CFTLib.ARL.isGalois_cyclotomicField_over_base
import Submission.NK.CFTLib.ARL.RelNormFI
import Submission.NK.CFTLib.ARL.cyclotomicCellKernelLe_B
import Submission.NK.CFTLib.ARLAlt.Setup
import Submission.NK.CFTLib.ARLAlt.CellAbelian
import Submission.NK.CFTLib.ARLAlt.AuxLocal
import Submission.NK.CFTLib.ARLAlt.CellAtAux
import Submission.NK.CFTLib.ARLAlt.Descent
import Submission.NK.CFTLib.ARLAlt.RestrictFrobenius
import Submission.NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension
import Submission.NK.Chebotarev.IsFrobAtPrimeAlgEquivSameBase
import Submission.NK.Chebotarev.ExistsUniqueIsFrobAtPrime
import Submission.NK.Existence.ArtinLemma.helpers
import Submission.NK.CFTLib.ArtinReciprocityIdeal.indexIdealCoprimeLeNormClassIndex
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField

/-!
# The transfer of Artin's lemma in the ideal-theoretic form

`NK.NUV2.ARL.kernelLeOfAuxField` is Lang, *Algebraic Number Theory*, Ch. X §2, Theorem 2
(Childress, *Class Field Theory*, Prop. 2.2): for a finite **cyclic** extension `L/K` of number
fields, a modulus `m > 0` containing all the primes ramified in `L/K` and the auxiliary-field
hypothesis `NK.CFTLib.ARL.AuxFieldHyp K L m` (Artin's lemma), every fractional ideal `A` of `K`
coprime to `(m)` with trivial Artin symbol lies in `P(m)·𝔑(m)`.

The proof is the transfer argument: `haux` applied to the support of `A` produces `M`, a field
`E ⊆ L(ζ_M)` with `E ⊓ L = K`, and for every `𝔭` in the support a subfield `E𝔭 ≤ E` with
`E𝔭 ⊔ ℚ(ζ_M) = L(ζ_M)` and `𝔭` splitting completely in `E𝔭/K`; then
`X𝔭 := 𝔭^{e𝔭}·𝔟^{-e𝔭s𝔭}` is a norm from `E𝔭` of an ideal whose Artin symbol in `E𝔭·L/E𝔭` is
trivial, hence lies in `P_{E𝔭}·𝔑_{E𝔭}` by the cyclotomic cell, and hence in `P_K(m)·𝔑_{L/K}(m)`
by norm descent.  Multiplying over `𝔭` and using `[L:K] ∣ Σ e𝔭 s𝔭` and
`𝔟^{[L:K]} = N_{L/K}(𝔟𝒪_L) ∈ 𝔑` finishes.

The auxiliary lemmas below are the pieces of the transfer; they are stated here in the namespace
`NK.NUV2.ARL` and are self-contained (they do not depend on the removed helpers of
`NK.CFTLib.ARL.kernelLe_of_auxField_B`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors IsMulCommutative

namespace NK.NUV2.ARL

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

/-- **Conjugation of `K`-automorphisms along a `K`-algebra isomorphism.** -/
noncomputable def conjHom {K L₁ L₂ : Type} [Field K] [Field L₁] [Field L₂] [Algebra K L₁]
    [Algebra K L₂] (e : L₁ ≃ₐ[K] L₂) : Gal(L₁/K) →* Gal(L₂/K) where
  toFun σ := e.symm.trans (σ.trans e)
  map_one' := by
    ext x
    simp [AlgEquiv.trans_apply]
  map_mul' σ τ := by
    ext x
    simp [AlgEquiv.trans_apply]

lemma conjHom_apply {K L₁ L₂ : Type} [Field K] [Field L₁] [Field L₂] [Algebra K L₁]
    [Algebra K L₂] (e : L₁ ≃ₐ[K] L₂) (σ : Gal(L₁/K)) (x : L₂) :
    conjHom e σ x = e (σ (e.symm x)) := by
  show (e.symm.trans (σ.trans e)) x = e (σ (e.symm x))
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply]

lemma conjHom_injective {K L₁ L₂ : Type} [Field K] [Field L₁] [Field L₂] [Algebra K L₁]
    [Algebra K L₂] (e : L₁ ≃ₐ[K] L₂) : Function.Injective (conjHom e) := by
  intro σ τ h
  have h2 : ∀ x : L₂, σ (e.symm x) = τ (e.symm x) := by
    intro x
    have h3 := congrArg (fun f : Gal(L₂/K) => f x) h
    rw [conjHom_apply, conjHom_apply] at h3
    exact e.injective h3
  ext z
  obtain ⟨x, rfl⟩ := e.symm.surjective z
  exact h2 x

/-- Conjugating a `K`-automorphism of `L₂` to `L₁` and back returns it. -/
theorem conjHom_symm_conjHom {K L₁ L₂ : Type} [Field K] [Field L₁] [Field L₂] [Algebra K L₁]
    [Algebra K L₂] (e : L₁ ≃ₐ[K] L₂) (σ : Gal(L₂/K)) :
    conjHom e (conjHom e.symm σ) = σ := by
  ext x
  rw [conjHom_apply, conjHom_apply]
  simp [AlgEquiv.trans_apply]

/-- **The ring of integers of an intermediate field of a number field is a number field.** -/
theorem isMulCommutative_LImage {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (Gal(L/K))] (M : ℕ) :
    IsMulCommutative (Gal(↥(NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M)/K)) := by
  have hinj : Function.Injective
      (conjHom (NK.CFTLib.ARLAlt.LImageEquiv (K := K) (L := L) M)) :=
    conjHom_injective _
  refine IsMulCommutative.of_comm (fun a b => ?_)
  exact hinj (by
    rw [map_mul, map_mul]
    exact IsMulCommutative.is_comm.comm _ _)

/-! ## The `K`-algebra structure on `↥B` induced by an inclusion `A ≤ B` -/

/-- **The `K`-algebra structure on `↥B` induced by the inclusion `↥A → ↥B`** for intermediate
fields `A ≤ B`. -/
noncomputable def algOfLe {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (A B : IntermediateField K Ω) (h : A ≤ B) : Algebra ↥A ↥B :=
  RingHom.toAlgebra ((IntermediateField.inclusion h).toRingHom)

lemma algOfLe_algebraMap_apply {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (A B : IntermediateField K Ω) (h : A ≤ B) (x : ↥A) :
    (@algebraMap ↥A ↥B _ _ (algOfLe A B h)) x = (IntermediateField.inclusion h) x := rfl

lemma isScalarTower_algOfLe {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (A B : IntermediateField K Ω) (h : A ≤ B) :
    letI := algOfLe A B h
    IsScalarTower K ↥A ↥B := by
  letI := algOfLe A B h
  refine ⟨fun x a b => ?_⟩
  have h1 : (@algebraMap ↥A ↥B _ _ (algOfLe A B h)) (algebraMap K ↥A x) =
      (algebraMap K ↥B x : ↥B) := by
    apply Subtype.ext
    show ((IntermediateField.inclusion h) (algebraMap K ↥A x) : Ω) =
      ((algebraMap K ↥B x : ↥B) : Ω)
    rw [IntermediateField.coe_inclusion, IntermediateField.coe_algebraMap_apply,
      IntermediateField.coe_algebraMap_apply]
  simp only [Algebra.smul_def, map_mul, h1]
  ring

lemma finiteDimensional_algOfLe {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (A B : IntermediateField K Ω) [FiniteDimensional K ↥B] (h : A ≤ B) :
    letI := algOfLe A B h
    FiniteDimensional ↥A ↥B := by
  letI := algOfLe A B h
  haveI hT : IsScalarTower K ↥A ↥B := isScalarTower_algOfLe A B h
  exact Module.Finite.of_restrictScalars_finite K ↥A ↥B

/-- **The chosen Frobenius transports along a `K`-algebra isomorphism.** -/
theorem frobAtPrime_conjHom {K L₁ L₂ : Type} [Field K] [NumberField K] [Field L₁]
    [NumberField L₁] [Field L₂] [NumberField L₂] [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂] [IsGalois K L₁] [IsGalois K L₂]
    (e : L₁ ≃ₐ[K] L₂) (hc₁ : ∀ a b : Gal(L₁/K), a * b = b * a)
    (p : NK.Chebotarev.PrimeIdeal K)
    (hram : ∀ P : NK.Chebotarev.PrimeIdeal L₁, P.asIdeal.LiesOver p.asIdeal →
      P.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    NK.Chebotarev.frobAtPrime (K := K) (L := L₂) p
      = conjHom e (NK.Chebotarev.frobAtPrime (K := K) (L := L₁) p) := by
  obtain ⟨σ, -, huniq⟩ := NK.Chebotarev.ExistsUniqueIsFrobAtPrime hc₁ p hram
  have h2 : conjHom e.symm (NK.Chebotarev.frobAtPrime (K := K) (L := L₂) p) = σ :=
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
      = conjHom e (NK.CFTLib.Arl.artinSym (K := K) (L := L₁) hc₁ A) := by
  classical
  letI : CommMonoid Gal(L₁/K) := NK.CFTLib.Arl.galCommMonoid hc₁
  letI : CommMonoid Gal(L₂/K) := NK.CFTLib.Arl.galCommMonoid hc₂
  letI : IsMulCommutative Gal(L₁/K) := ⟨⟨hc₁⟩⟩
  letI : IsMulCommutative Gal(L₂/K) := ⟨⟨hc₂⟩⟩
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
  have key : ∀ p : NK.Chebotarev.PrimeIdeal K,
      (m : NumberField.RingOfIntegers K) ∉ p.asIdeal →
      NK.Chebotarev.frobAtPrime (K := K) (L := L₂) p
        = conjHom e (NK.Chebotarev.frobAtPrime (K := K) (L := L₁) p) := by
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
        = conjHom e
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
          conjHom e
            (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₁) hc₁
              ((NK.CFTLib.ARL.primeUnit p) ^ (NK.CFTLib.Arl.exps A p))) :=
        Finset.prod_congr rfl hstep
    _ = conjHom e
          (∏ p ∈ (NK.CFTLib.Arl.exps A).support,
            NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₁) hc₁
              ((NK.CFTLib.ARL.primeUnit p) ^ (NK.CFTLib.Arl.exps A p))) :=
        (map_prod (conjHom e) _ _).symm
    _ = conjHom e
          (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₁) hc₁
            (∏ p ∈ (NK.CFTLib.Arl.exps A).support,
              (NK.CFTLib.ARL.primeUnit p) ^ (NK.CFTLib.Arl.exps A p))) :=
        (congrArg (conjHom e)
          (map_prod (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := L₁) hc₁)
            _ _)).symm
    _ = conjHom e (NK.CFTLib.Arl.artinSym (K := K) (L := L₁) hc₁
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

/-- **The norm group of fractional ideals is monotone under a `K`-algebra isomorphism**: the norm
group of `L₂` is contained in that of `L₁` when `L₁ ≃ₐ[K] L₂`. -/
theorem normIdeals_le_of_algEquiv {K L₁ L₂ : Type} [Field K] [NumberField K] [Field L₁]
    [NumberField L₁] [Field L₂] [NumberField L₂] [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂] (e : L₁ ≃ₐ[K] L₂) (m : ℕ) :
    NK.CFTLib.ARL.normIdeals K L₂ m ≤ NK.CFTLib.ARL.normIdeals K L₁ m := by
  classical
  rw [NK.CFTLib.ARL.normIdeals, Subgroup.closure_le]
  rintro A ⟨𝔅, rfl⟩
  set σ : 𝓞 L₁ ≃+* 𝓞 L₂ := (NumberField.RingOfIntegers.mapAlgEquiv e).toRingEquiv with hσ
  have hfsurj : Function.Surjective σ.toRingHom := σ.surjective
  have hcomap : ∀ I : Ideal (𝓞 L₂), Ideal.map σ.toRingHom (Ideal.comap σ.toRingHom I) = I :=
    fun I => Ideal.map_comap_of_surjective σ.toRingHom hfsurj I
  obtain ⟨h1, h2⟩ : ((𝔅 : Ideal (𝓞 L₂)).comap σ.toRingHom) ≠ ⊥ ∧
      ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 L₁), (m : 𝓞 L₁) ∈ 𝔭.asIdeal →
        ¬ 𝔭.asIdeal ∣ (𝔅 : Ideal (𝓞 L₂)).comap σ.toRingHom := by
    constructor
    · intro h
      have : (𝔅 : Ideal (𝓞 L₂)) = ⊥ := by
        rw [← hcomap (𝔅 : Ideal (𝓞 L₂)), h, Ideal.map_bot]
      exact 𝔅.2.1 this
    · intro 𝔭 h𝔭 hdvd
      have hmem : (m : 𝓞 L₂) ∈ Ideal.map σ.toRingHom 𝔭.asIdeal := by
        rw [show (m : 𝓞 L₂) = σ.toRingHom (m : 𝓞 L₁) from (map_natCast σ.toRingHom m).symm]
        exact Ideal.mem_map_of_mem _ h𝔭
      have hprime : (Ideal.map σ.toRingHom 𝔭.asIdeal).IsPrime := by
        haveI := 𝔭.isPrime
        exact Ideal.map_isPrime_of_equiv σ
      have hne : Ideal.map σ.toRingHom 𝔭.asIdeal ≠ ⊥ :=
        fun h => 𝔭.ne_bot ((Ideal.map_eq_bot_iff_of_injective σ.injective).mp h)
      have hnot := 𝔅.2.2 ⟨Ideal.map σ.toRingHom 𝔭.asIdeal, hprime, hne⟩ hmem
      apply hnot
      rw [Ideal.dvd_iff_le] at hdvd ⊢
      calc (𝔅 : Ideal (𝓞 L₂)) =
            Ideal.map σ.toRingHom (Ideal.comap σ.toRingHom (𝔅 : Ideal (𝓞 L₂))) :=
            (hcomap (𝔅 : Ideal (𝓞 L₂))).symm
        _ ≤ Ideal.map σ.toRingHom 𝔭.asIdeal := Ideal.map_mono hdvd
  refine Subgroup.subset_closure ⟨⟨(𝔅 : Ideal (𝓞 L₂)).comap σ.toRingHom, h1, h2⟩, ?_⟩
  apply Units.ext
  simp only [Units.val_mk0]
  rw [show (Ideal.comap σ.toRingHom (𝔅 : Ideal (𝓞 L₂))) = (𝔅 : Ideal (𝓞 L₂)).comap
        (NumberField.RingOfIntegers.mapAlgEquiv e) from rfl,
    Ideal.relNorm_comap_algEquiv]

/-- **The norm ray of `L₂` is contained in that of `L₁`** for `L₁ ≃ₐ[K] L₂`, in the
`NK.CFTLib.ArtinReciprocityIdeal` vocabulary. -/
theorem normRay_le_of_algEquiv {K L₁ L₂ : Type} [Field K] [NumberField K] [Field L₁]
    [NumberField L₁] [Field L₂] [NumberField L₂] [Algebra K L₁] [Algebra K L₂]
    [FiniteDimensional K L₁] [FiniteDimensional K L₂] (e : L₁ ≃ₐ[K] L₂) (m : ℕ) :
    NK.CFTLib.ArtinReciprocityIdeal.normRay K L₂ m ≤
      NK.CFTLib.ArtinReciprocityIdeal.normRay K L₁ m := by
  rw [NK.CFTLib.ArtinReciprocityIdeal.normRay_eq_normIdeals,
    NK.CFTLib.ArtinReciprocityIdeal.normRay_eq_normIdeals]
  exact normIdeals_le_of_algEquiv e m

/-- **The Artin symbol is compatible with the relative norm**, in the form used by the transfer:
for intermediate fields `E, L` of a finite Galois extension `M/K` with `E ⊓ L = K`, the
restriction to `L` of `ψ_{M/E}(𝔄)` is `ψ_{L/K}(N_{E/K}𝔄)`. -/
theorem artinSym_restrict_relNorm' {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (E L : IntermediateField K M) [FiniteDimensional K ↥E] [NumberField ↥E]
    [FiniteDimensional K ↥L] [NumberField ↥L] [IsGalois K ↥L]
    (hcommE : ∀ a b : M ≃ₐ[↥E] M, a * b = b * a)
    (hcommL : ∀ a b : (↥L ≃ₐ[K] ↥L), a * b = b * a)
    (m : ℕ)
    (hramE : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥E,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E) (L := M) 𝔮 →
      (m : 𝓞 ↥E) ∈ 𝔮.asIdeal)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥L) p →
      (m : 𝓞 K) ∈ p.asIdeal)
    (𝔄 : (FractionalIdeal (𝓞 ↥E)⁰ ↥E)ˣ)
    (hcop : NK.CFTLib.ArtinReciprocityIdeal.FracCoprime (K := ↥E) m 𝔄) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L
        ((NK.CFTLib.Arl.artinSym (K := ↥E) (L := M) hcommE
            (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)).restrictScalars K)
      = NK.CFTLib.Arl.artinSym (K := K) (L := ↥L) hcommL
          (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥E) 𝔄) := by
  classical
  letI hMC_E : IsMulCommutative (M ≃ₐ[↥E] M) := ⟨⟨hcommE⟩⟩
  letI hMC_L : IsMulCommutative (↥L ≃ₐ[K] ↥L) := ⟨⟨hcommL⟩⟩
  let Φ : (M ≃ₐ[↥E] M) →* (↥L ≃ₐ[K] ↥L) :=
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L).comp (AlgEquiv.restrictScalarsHom K)
  let F : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E →* (↥L ≃ₐ[K] ↥L) :=
    Φ.comp (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := ↥E) (L := M) hcommE)
  let G : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E →* (↥L ≃ₐ[K] ↥L) :=
    (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥L) hcommL).comp
      (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥E))
  have hFG : F 𝔄 = G 𝔄 := by
    set S : Finset (NK.Chebotarev.PrimeIdeal ↥E) :=
      (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (K := ↥E)
        (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E))).toFinset with hS
    have hSmem : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥E,
        𝔮 ∈ S ↔ FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) ≠ 0 :=
      fun 𝔮 => Set.Finite.mem_toFinset _
    have hsupp : Function.mulSupport (fun 𝔮 : NK.Chebotarev.PrimeIdeal ↥E =>
        ((𝔮.asIdeal : Ideal (𝓞 ↥E)) : FractionalIdeal (𝓞 ↥E)⁰ ↥E) ^
          FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) ⊆ ↑S := by
      intro 𝔮 h𝔮
      exact (hSmem 𝔮).mpr fun h0 => h𝔮 (by simp only [h0, zpow_zero])
    have hfac : (∏ 𝔮 ∈ S, (NK.CFTLib.ARL.primeUnit 𝔮) ^
        FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) = 𝔄 := by
      apply Units.ext
      rw [Units.coe_prod]
      simp only [NK.CFTLib.ARL.primeUnit_val, Units.val_zpow_eq_zpow_val]
      rw [← finprod_eq_prod_of_mulSupport_subset _ hsupp]
      exact FractionalIdeal.finprod_heightOneSpectrum_factorization' ↥E 𝔄.ne_zero
    have hprime : ∀ 𝔮 ∈ S, F (NK.CFTLib.ARL.primeUnit 𝔮)
        = G (NK.CFTLib.ARL.primeUnit 𝔮) := by
      intro 𝔮 h𝔮
      have hcount : FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) ≠ 0 :=
        (hSmem 𝔮).mp h𝔮
      have hunrE : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E) (L := M) 𝔮 := by
        by_contra h
        exact hcount (hcop 𝔮 (hramE 𝔮 h))
      have hunrL : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥L)
          (𝔮.under (𝓞 K)) := by
        by_contra h
        have hm : (m : 𝓞 K) ∈ (𝔮.under (𝓞 K)).asIdeal := hram (𝔮.under (𝓞 K)) h
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal] at hm
        have hm' : (m : 𝓞 ↥E) ∈ 𝔮.asIdeal := by
          have h2 := (Ideal.mem_under (𝓞 K) 𝔮.asIdeal).mp hm
          simpa using h2
        exact hcount (hcop 𝔮 hm')
      have hF : F (NK.CFTLib.ARL.primeUnit 𝔮) = AlgEquiv.restrictNormalHom (F := K)
          (K₁ := M) L
          ((NK.Chebotarev.frobAtPrime (K := ↥E) (L := M) 𝔮).restrictScalars K) := by
        change Φ (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := ↥E) (L := M) hcommE
          (NK.CFTLib.ARL.primeUnit 𝔮)) = _
        rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
          NK.CFTLib.ARL.primeUnit_val, NK.CFTLib.Arl.artinSym_prime]
        rfl
      have hG : G (NK.CFTLib.ARL.primeUnit 𝔮) = (NK.Chebotarev.frobAtPrime (K := K)
          (L := ↥L) (𝔮.under (𝓞 K))) ^ (𝔮.asIdeal.inertiaDeg (𝓞 K)) := by
        haveI : 𝔮.asIdeal.IsMaximal :=
          Ring.DimensionLEOne.maximalOfPrime 𝔮.ne_bot 𝔮.isPrime
        have hqne : (𝔮.under (𝓞 K)).asIdeal ≠ ⊥ := by
          rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
          exact Ideal.under_ne_bot (𝓞 K) 𝔮.ne_bot
        haveI : ((𝔮.under (𝓞 K)).asIdeal).IsMaximal :=
          Ring.DimensionLEOne.maximalOfPrime hqne inferInstance
        haveI : 𝔮.asIdeal.LiesOver (𝔮.under (𝓞 K)).asIdeal :=
          ⟨IsDedekindDomain.HeightOneSpectrum.under_asIdeal (𝓞 K) 𝔮⟩
        change NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥L) hcommL
          (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥E)
            (NK.CFTLib.ARL.primeUnit 𝔮)) = _
        rw [NK.CFTLib.ARL.relNormUnit_primeUnit,
          NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply, Units.val_mk0,
          Ideal.relNorm_eq_pow_of_isMaximal 𝔮.asIdeal ((𝔮.under (𝓞 K)).asIdeal),
          FractionalIdeal.coeIdeal_pow,
          NK.CFTLib.ArtinReciprocityIdeal.artinSymFrac_pow hcommL
            (FractionalIdeal.coeIdeal_ne_zero.mpr ((𝔮.under (𝓞 K)).ne_bot)),
          NK.CFTLib.Arl.artinSym_prime]
      rw [hF, hG]
      exact NK.CFTLib.ArtinReciprocityIdeal.restrict_frobAtPrime_eq E L hcommE hcommL 𝔮
        hunrE hunrL
    calc F 𝔄 = F (∏ 𝔮 ∈ S, (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) := by rw [hfac]
      _ = ∏ 𝔮 ∈ S, F (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) := by
          rw [map_prod]
          exact Finset.prod_congr rfl fun 𝔮 _ => map_zpow _ _ _
      _ = ∏ 𝔮 ∈ S, G (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) :=
          Finset.prod_congr rfl fun 𝔮 h𝔮 => by rw [hprime 𝔮 h𝔮]
      _ = G (∏ 𝔮 ∈ S, (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) := by
          rw [map_prod]
          exact Finset.prod_congr rfl fun 𝔮 _ => (map_zpow _ _ _).symm
      _ = G 𝔄 := by rw [hfac]
  simpa only [F, G, Φ, MonoidHom.comp_apply,
    NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
    AlgEquiv.restrictScalarsHom_apply] using hFG

/-- **`L`, viewed inside `Ω = L(ζ_M)`, is unramified at `p` over `K` whenever `p` is prime to
`(m·M)`**, where `m` is a modulus containing all the ramified primes of `L/K`. -/
theorem isUnramified_LImage {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (M : ℕ) [NeZero M] (m : ℕ)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p →
      (m : 𝓞 K) ∈ p.asIdeal)
    (p : NK.Chebotarev.PrimeIdeal K) (hpm : (m : 𝓞 K) ∉ p.asIdeal)
    (hpM : (M : 𝓞 K) ∉ p.asIdeal) :
    NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K)
      (L := ↥(NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M)) p := by
  set L' : IntermediateField K (CyclotomicField M L) :=
    NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M with hL'
  have hunrL : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p := by
    by_contra h
    exact hpm (hram p h)
  intro P' hP'
  have key : ∀ 𝔓 : NK.Chebotarev.PrimeIdeal (CyclotomicField M L),
      𝔓.asIdeal.LiesOver p.asIdeal →
      𝔓.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    intro 𝔓 h𝔓
    set 𝔮 : IsDedekindDomain.HeightOneSpectrum (𝓞 L) := 𝔓.under (𝓞 L) with h𝔮
    have h𝔮lies : 𝔮.asIdeal.LiesOver p.asIdeal :=
      Ideal.LiesOver.mk (by rw [h𝔮]; exact h𝔓.over)
    have hM𝔮 : (M : 𝓞 L) ∉ 𝔮.asIdeal := by
      intro hmem
      refine hpM ?_
      rw [h𝔮lies.over]
      exact (Ideal.mem_under (𝓞 K) 𝔮.asIdeal).mpr (by rw [map_natCast]; exact hmem)
    have h1 : 𝔮.asIdeal.ramificationIdx (𝓞 K) = 1 := hunrL 𝔮 h𝔮lies
    have h2 : 𝔓.asIdeal.ramificationIdx (𝓞 L) = 1 :=
      NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (k := L)
        (Ω := CyclotomicField M L) M 𝔮 hM𝔮 𝔓 (by rw [h𝔮]; exact ⟨rfl⟩)
    haveI : 𝔓.asIdeal.LiesOver 𝔮.asIdeal := by rw [h𝔮]; exact ⟨rfl⟩
    have htower := Ideal.ramificationIdx_tower (R := 𝓞 K) (S := 𝓞 L)
      (T := 𝓞 (CyclotomicField M L)) (q := 𝔮.asIdeal) (r := 𝔓.asIdeal)
    rw [h1, h2, one_mul] at htower
    exact htower
  obtain ⟨𝔓, h𝔓⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
    (K := ↥L') (L := CyclotomicField M L) P'
  have h𝔓p : 𝔓.asIdeal.LiesOver p.asIdeal :=
    Ideal.LiesOver.trans (𝔓 := 𝔓.asIdeal) (P := P'.asIdeal) (p := p.asIdeal)
  have h1 : 𝔓.asIdeal.ramificationIdx (𝓞 K) = 1 := key 𝔓 h𝔓p
  haveI := h𝔓
  have htower := Ideal.ramificationIdx_tower (R := 𝓞 K) (S := 𝓞 ↥L')
    (T := 𝓞 (CyclotomicField M L)) (q := P'.asIdeal) (r := 𝔓.asIdeal)
  rw [h1] at htower
  exact Nat.eq_one_of_mul_eq_one_right htower.symm

/-- **The cell `E·L` of the transfer is unramified over `E` at the primes not dividing the
cyclotomic level `M`.** -/
theorem isUnramified_cellAtAux {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (M : ℕ) [NeZero M] (E : IntermediateField K (CyclotomicField M L))
    (hsup : (E.restrictScalars ℚ) ⊔ (IntermediateField.adjoin ℚ
      ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} : Set (CyclotomicField M L))) = ⊤)
    (q : NK.Chebotarev.PrimeIdeal ↥E) (hq : (M : 𝓞 ↥E) ∉ q.asIdeal) :
    NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E)
      (L := ↥(NK.CFTLib.ARLAlt.ofLe E
        (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left)) q := by
  intro Q hQ
  haveI hcyc : IsCyclotomicExtension {M} ↥E (CyclotomicField M L) :=
    NK.CFTLib.ARLAlt.isCyclotomicExtension_of_sup_adjoin_zeta (K := K) (L := L) M E hsup
  haveI hnfC : NumberField ↥(NK.CFTLib.ARLAlt.ofLe E
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left) :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField _
  obtain ⟨P, hP⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
    (K := ↥(NK.CFTLib.ARLAlt.ofLe E (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M)
      le_sup_left)) (L := CyclotomicField M L) Q
  have hPq : P.asIdeal.LiesOver q.asIdeal :=
    Ideal.LiesOver.trans (𝔓 := P.asIdeal) (P := Q.asIdeal) (p := q.asIdeal)
  have hunrΩ : P.asIdeal.ramificationIdx (𝓞 ↥E) = 1 :=
    NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (k := ↥E)
      (Ω := CyclotomicField M L) M q hq P hPq
  haveI := hP
  have htower := Ideal.ramificationIdx_tower (R := 𝓞 ↥E)
    (S := 𝓞 ↥(NK.CFTLib.ARLAlt.ofLe E (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M)
      le_sup_left)) (T := 𝓞 (CyclotomicField M L)) (q := Q.asIdeal) (r := P.asIdeal)
  rw [hunrΩ] at htower
  exact Nat.eq_one_of_mul_eq_one_right htower.symm

/-- **A prime of `L` above any prime of `K` exists** (without a Galois hypothesis). -/
theorem exists_primeIdeal_liesOver' {K' L' : Type} [Field K'] [NumberField K'] [Field L']
    [NumberField L'] [Algebra K' L'] (p : NK.Chebotarev.PrimeIdeal K') :
    ∃ P : NK.Chebotarev.PrimeIdeal L', P.asIdeal.LiesOver p.asIdeal := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (p.asIdeal.primesOver
    (NumberField.RingOfIntegers L')))
  exact ⟨⟨P.1, P.2.1, Ideal.ne_bot_of_mem_primesOver p.ne_bot P.2⟩, P.2.2⟩

/-- **Unramifiedness passes to subextensions** (in the `ofLe` presentation). -/
theorem isUnramified_ofLe_of_isUnramified {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (M : ℕ) [NeZero M]
    (E LE : IntermediateField K (CyclotomicField M L)) (h : E ≤ LE)
    (𝔮 : NK.Chebotarev.PrimeIdeal ↥E)
    (hunr : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E)
      (L := CyclotomicField M L) 𝔮) :
    NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E)
      (L := ↥(NK.CFTLib.ARLAlt.ofLe E LE h)) 𝔮 := by
  intro Q hQ
  obtain ⟨P, hP⟩ := exists_primeIdeal_liesOver'
    (K' := ↥(NK.CFTLib.ARLAlt.ofLe E LE h)) (L' := CyclotomicField M L) Q
  have hPq : P.asIdeal.LiesOver 𝔮.asIdeal := by
    refine ⟨?_⟩
    show 𝔮.asIdeal = (P.asIdeal.under (NumberField.RingOfIntegers ↥(NK.CFTLib.ARLAlt.ofLe E LE h))).under
      (NumberField.RingOfIntegers ↥E)
    rw [← hP.over, hQ.over]
  have h1 : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥E) = 1 := hunr P hPq
  haveI : P.asIdeal.LiesOver Q.asIdeal := hP
  have hdvd : Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ↥E) ∣ 1 := by
    rw [← h1]
    exact Ideal.ramificationIdx_below_dvd (R := NumberField.RingOfIntegers ↥E)
      (S := NumberField.RingOfIntegers ↥(NK.CFTLib.ARLAlt.ofLe E LE h))
      (T := NumberField.RingOfIntegers (CyclotomicField M L)) (q := Q.asIdeal) (r := P.asIdeal)
  exact Nat.eq_one_of_dvd_one hdvd

/-- **The restriction map `Gal(E·L/E) → Gal(L/K)` in the `restrictNormalHom` presentation.** -/
theorem restrictRestrictAlgEquivMapHom_eq_restrict {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (M : ℕ) [NeZero M] (E : IntermediateField K (CyclotomicField M L)) :
    IntermediateField.restrictRestrictAlgEquivMapHom K
        ↥(NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) ↥E (CyclotomicField M L)
      = (AlgEquiv.restrictNormalHom (F := K) (K₁ := CyclotomicField M L)
          (NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M)).comp (AlgEquiv.restrictScalarsHom K) := by
  refine MonoidHom.ext fun φ => ?_
  refine AlgEquiv.ext fun x => ?_
  refine Subtype.ext ?_
  rw [IntermediateField.restrictRestrictAlgEquivMapHom_apply, MonoidHom.comp_apply,
    AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictScalarsHom_apply]
  rfl

/-- **An `↥E`-automorphism of `Ω` which restricts to `1` on `L` restricts to `1` on `E·L`.** -/
theorem restrictNormalHom_eq_one_of_sup {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (M : ℕ) [NeZero M] (E : IntermediateField K (CyclotomicField M L))
    [IsGalois ↥E ↥(NK.CFTLib.ARLAlt.ofLe E
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left)]
    (σ : Gal((CyclotomicField M L)/↥E))
    (hσ : AlgEquiv.restrictNormalHom (F := K) (K₁ := CyclotomicField M L)
        (NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) (σ.restrictScalars K) = 1) :
    AlgEquiv.restrictNormalHom (F := ↥E) (K₁ := CyclotomicField M L)
        ↥(NK.CFTLib.ARLAlt.ofLe E
          (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left) σ = 1 := by
  classical
  set LΩ := NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M with hLΩ
  haveI : IsGalois K ↥LΩ := NK.CFTLib.ARLAlt.isGalois_LImage (K := K) (L := L) M
  have hL : AlgEquiv.restrictScalars K σ ∈
      (LΩ : IntermediateField K (CyclotomicField M L)).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h1 : (AlgEquiv.restrictNormalHom (F := K) (K₁ := CyclotomicField M L) LΩ
        (σ.restrictScalars K)) ⟨x, hx⟩ = ⟨x, hx⟩ := by rw [hσ]; rfl
    have h2 := AlgEquiv.restrictNormalHom_apply (F := K) (K₁ := CyclotomicField M L) LΩ
      (σ.restrictScalars K) ⟨x, hx⟩
    rw [h1] at h2
    exact h2.symm
  have hE : AlgEquiv.restrictScalars K σ ∈
      (E : IntermediateField K (CyclotomicField M L)).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    exact σ.commutes ⟨y, hy⟩
  have h3 : AlgEquiv.restrictScalars K σ ∈
      ((E ⊔ LΩ : IntermediateField K (CyclotomicField M L))).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hE, hL⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at h3
  have hkey : AlgEquiv.restrictNormalHom (F := ↥E) (K₁ := CyclotomicField M L)
      ↥(NK.CFTLib.ARLAlt.ofLe E (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M)
        le_sup_left) σ
      = σ.restrictNormal ↥(NK.CFTLib.ARLAlt.ofLe E
        (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left) := rfl
  rw [hkey, AlgEquiv.restrictNormal_eq_one_iff]
  intro x hx
  simpa using h3 x hx

/-- **The Artin symbol of `Ω/↥E` restricts to the Artin symbol of `E·L/↥E`.** -/
theorem restrictNormalHom_artinSym_eq_ofLe {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (M : ℕ) [NeZero M] (E : IntermediateField K (CyclotomicField M L))
    [IsGalois ↥E (CyclotomicField M L)]
    [IsMulCommutative (Gal((CyclotomicField M L)/↥E))]
    [IsGalois ↥E ↥(NK.CFTLib.ARLAlt.ofLe E
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left)]
    [IsMulCommutative (Gal(↥(NK.CFTLib.ARLAlt.ofLe E
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left)/↥E))]
    (hcommΩ : ∀ a b : Gal((CyclotomicField M L)/↥E), a * b = b * a)
    (hcommC : ∀ a b : Gal(↥(NK.CFTLib.ARLAlt.ofLe E
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left)/↥E), a * b = b * a)
    (c : ℕ)
    (hram : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥E,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E)
        (L := CyclotomicField M L) 𝔮 →
      (c : NumberField.RingOfIntegers ↥E) ∈ 𝔮.asIdeal)
    (𝔄 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E)
    (hcop : NK.CFTLib.ArtinReciprocityIdeal.FracCoprime (K := ↥E) c 𝔄) :
    AlgEquiv.restrictNormalHom (F := ↥E) (K₁ := CyclotomicField M L)
        ↥(NK.CFTLib.ARLAlt.ofLe E
          (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left)
        (NK.CFTLib.Arl.artinSym (K := ↥E) (L := CyclotomicField M L) hcommΩ
          (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E))
      = NK.CFTLib.Arl.artinSym (K := ↥E)
          (L := ↥(NK.CFTLib.ARLAlt.ofLe E
            (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left)) hcommC
          (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) := by
  classical
  let LE := E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M
  letI hMCΩ : IsMulCommutative (Gal((CyclotomicField M L)/↥E)) := ⟨⟨hcommΩ⟩⟩
  letI hMCC : IsMulCommutative (Gal(↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)/↥E)) := ⟨⟨hcommC⟩⟩
  let F : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E →*
      Gal(↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)/↥E) :=
    (AlgEquiv.restrictNormalHom (F := ↥E) (K₁ := CyclotomicField M L)
      ↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)).comp
      (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := ↥E)
        (L := CyclotomicField M L) hcommΩ)
  let G : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E →*
      Gal(↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)/↥E) :=
    NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := ↥E)
      (L := ↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)) hcommC
  have hFG : F 𝔄 = G 𝔄 := by
    set S : Finset (NK.Chebotarev.PrimeIdeal ↥E) :=
      (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (K := ↥E)
        (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E))).toFinset with hS
    have hSmem : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥E,
        𝔮 ∈ S ↔ FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) ≠ 0 :=
      fun 𝔮 => Set.Finite.mem_toFinset _
    have hsupp : Function.mulSupport (fun 𝔮 : NK.Chebotarev.PrimeIdeal ↥E =>
        ((𝔮.asIdeal : Ideal (𝓞 ↥E)) : FractionalIdeal (𝓞 ↥E)⁰ ↥E) ^
          FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) ⊆ ↑S := by
      intro 𝔮 h𝔮
      exact (hSmem 𝔮).mpr fun h0 => h𝔮 (by simp only [h0, zpow_zero])
    have hfac : (∏ 𝔮 ∈ S, (NK.CFTLib.ARL.primeUnit 𝔮) ^
        FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) = 𝔄 := by
      apply Units.ext
      rw [Units.coe_prod]
      simp only [NK.CFTLib.ARL.primeUnit_val, Units.val_zpow_eq_zpow_val]
      rw [← finprod_eq_prod_of_mulSupport_subset _ hsupp]
      exact FractionalIdeal.finprod_heightOneSpectrum_factorization' ↥E 𝔄.ne_zero
    have hprime : ∀ 𝔮 ∈ S, F (NK.CFTLib.ARL.primeUnit 𝔮)
        = G (NK.CFTLib.ARL.primeUnit 𝔮) := by
      intro 𝔮 h𝔮
      have hcount : FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) ≠ 0 :=
        (hSmem 𝔮).mp h𝔮
      have hunrΩ : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E)
          (L := CyclotomicField M L) 𝔮 := by
        by_contra h
        exact hcount (hcop 𝔮 (hram 𝔮 h))
      have hunrC : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E)
          (L := ↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)) 𝔮 :=
        isUnramified_ofLe_of_isUnramified (K := K) (L := L) M E LE le_sup_left 𝔮 hunrΩ
      have hF : F (NK.CFTLib.ARL.primeUnit 𝔮) =
          AlgEquiv.restrictNormalHom (F := ↥E) (K₁ := CyclotomicField M L)
            ↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)
            (NK.Chebotarev.frobAtPrime (K := ↥E) (L := CyclotomicField M L) 𝔮) := by
        change AlgEquiv.restrictNormalHom (F := ↥E) (K₁ := CyclotomicField M L)
            ↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)
            (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := ↥E)
              (L := CyclotomicField M L) hcommΩ (NK.CFTLib.ARL.primeUnit 𝔮)) = _
        rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
          NK.CFTLib.ARL.primeUnit_val, NK.CFTLib.Arl.artinSym_prime]
      have hG : G (NK.CFTLib.ARL.primeUnit 𝔮) =
          NK.Chebotarev.frobAtPrime (K := ↥E)
            (L := ↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)) 𝔮 := by
        change NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := ↥E)
          (L := ↥(NK.CFTLib.ARLAlt.ofLe E LE le_sup_left)) hcommC
          (NK.CFTLib.ARL.primeUnit 𝔮) = _
        rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
          NK.CFTLib.ARL.primeUnit_val, NK.CFTLib.Arl.artinSym_prime]
      rw [hF, hG]
      exact NK.CFTLib.ARLAlt.restrictNormalHom_frobAtPrime_ofLe (K := K) (L := L) M E LE
        le_sup_left le_sup_right rfl 𝔮 hunrC
    calc F 𝔄 = F (∏ 𝔮 ∈ S, (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) := by rw [hfac]
      _ = ∏ 𝔮 ∈ S, F (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) := by
          rw [map_prod]
          exact Finset.prod_congr rfl fun 𝔮 _ => map_zpow _ _ _
      _ = ∏ 𝔮 ∈ S, G (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) :=
          Finset.prod_congr rfl fun 𝔮 h𝔮 => by rw [hprime 𝔮 h𝔮]
      _ = G (∏ 𝔮 ∈ S, (NK.CFTLib.ARL.primeUnit 𝔮) ^
            FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E)) := by
          rw [map_prod]
          exact Finset.prod_congr rfl fun 𝔮 _ => (map_zpow _ _ _).symm
      _ = G 𝔄 := by rw [hfac]
  simpa only [F, G, MonoidHom.comp_apply,
    NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply] using hFG

/-- **The norm ray of `Ω/K` at the image `LΩ` of `L` is the norm ray of `L/K`.** -/
theorem normRay_LImage_eq {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (M : ℕ) [NeZero M] (m : ℕ) :
    NK.CFTLib.ArtinReciprocityIdeal.normRay K
        ↥(NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) m
      = NK.CFTLib.ArtinReciprocityIdeal.normRay K L m :=
  le_antisymm
    (normRay_le_of_algEquiv (NK.CFTLib.ARLAlt.LImageEquiv (K := K) (L := L) M).symm m)
    (normRay_le_of_algEquiv (NK.CFTLib.ARLAlt.LImageEquiv (K := K) (L := L) M) m)

/-- **Descent of the norm ray from the cyclotomic cell.**  The relative norm `N_{E/K}` maps the
norm ray of the cell `E·L/E` into the norm ray of `L/K`. -/
theorem normRay_cell_descent {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (M : ℕ) [NeZero M] (E : IntermediateField K (CyclotomicField M L))
    [FiniteDimensional ↥E ↥(NK.CFTLib.ARLAlt.ofLe E
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left)]
    [FiniteDimensional K ↥E] [NumberField ↥E]
    (c m : ℕ) (hm : 0 < m) (hcm : m ∣ c) :
    (NK.CFTLib.ArtinReciprocityIdeal.normRay ↥E
        ↥(NK.CFTLib.ARLAlt.ofLe E
          (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left) c).map
      (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥E))
      ≤ NK.CFTLib.ArtinReciprocityIdeal.normRay K L m := by
  letI : Algebra ↥E ↥(NK.CFTLib.ARLAlt.ofLe
      (NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M)
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_right) :=
    inferInstanceAs (Algebra ↥E ↥(NK.CFTLib.ARLAlt.ofLe E
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left))
  letI : IsScalarTower K ↥E ↥(NK.CFTLib.ARLAlt.ofLe
      (NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M)
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_right) :=
    inferInstanceAs (IsScalarTower K ↥E ↥(NK.CFTLib.ARLAlt.ofLe E
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_left))
  have h := NK.CFTLib.ARLAlt.normRay_map_relNormUnit_le (K := K)
    (L := ↥(NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M))
    (E := ↥E) (LE := ↥(NK.CFTLib.ARLAlt.ofLe
      (NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M)
      (E ⊔ NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M) le_sup_right)) c m hm hcm
  refine le_trans (le_of_eq ?_) (le_trans h ?_)
  · rfl
  · rw [normRay_LImage_eq (K := K) (L := L) M m]

/-! ## The transfer: `ker ψ ∩ I(m) ⊆ P(m)·𝔑(m)` -/

theorem kernelLeOfAuxField (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
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
  haveI hgalΩ : IsGalois K (CyclotomicField M L) :=
    NK.CFTLib.ARL.isGalois_cyclotomicField_over_base (K := K) (L := L) M
  -- ## `LΩ` and its Galois theory
  haveI hcommΩ : IsMulCommutative (Gal(↥LΩ/K)) :=
    isMulCommutative_LImage (K := K) (L := L) M
  have hcommΩ' : ∀ a b : Gal(↥LΩ/K), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
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
      push Not at hc
      exact hp (isUnramified_LImage (K := K) (L := L) M m hram p hc.1 hc.2)
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
  have hsurj := IntermediateField.restrictRestrictAlgEquivMapHom_surjective (F := K)
    (E := CyclotomicField M L) LΩ E (by rw [inf_comm]; exact hdisj)
  obtain ⟨τ, hτ⟩ := hsurj σ
  have hτ' : (AlgEquiv.restrictNormalHom (F := K) (K₁ := CyclotomicField M L) ↥LΩ)
      (AlgEquiv.restrictScalars K τ) = σ := by
    have hh := hτ
    rw [restrictRestrictAlgEquivMapHom_eq_restrict (K := K) (L := L) M E] at hh
    exact hh
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
    have h := artinSym_restrict_relNorm' (K := K) (M := CyclotomicField M L)
      E LΩ (fun a b : Gal(CyclotomicField M L/↥E) => IsMulCommutative.is_comm.comm a b)
      hcommΩ' 𝔪 hramE hramLΩ (𝔅 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E) hcop𝔅
    rw [h𝔅, hτ'] at h
    exact h.symm
  have hcop𝔟 : NK.CFTLib.ArtinReciprocityIdeal.FracCoprime 𝔪 𝔟 :=
    fracCoprime_relNormUnit (K := K) (L := ↥E) hcop𝔅
  -- ## the per-prime elements `X 𝔭`
  let Xa : NK.Chebotarev.PrimeIdeal K → NK.CFTLib.ArtinReciprocityIdeal.Frac K := fun 𝔭 =>
    (NK.CFTLib.ARL.primeUnit 𝔭) ^ (NK.CFTLib.Arl.exps Afr) 𝔭 *
      𝔟 ^ (-((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭))
  have hXmem : ∀ 𝔭 ∈ s, Xa 𝔭 ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
      NK.CFTLib.ArtinReciprocityIdeal.normRay K L m := by
    intro 𝔭 h𝔭
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
    haveI hgalC𝔭 : IsGalois ↥(Ef ⟨𝔭, h𝔭⟩) ↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩)
        (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left) :=
      NK.CFTLib.ARLAlt.isGalois_ofLe_sup (K := K) (L := L) M (Ef ⟨𝔭, h𝔭⟩)
    haveI hmcCell : IsMulCommutative (Gal(↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩)
        (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left)/↥(Ef ⟨𝔭, h𝔭⟩))) :=
      NK.CFTLib.ARLAlt.isMulCommutative_ofLe_sup (K := K) (L := L) M (Ef ⟨𝔭, h𝔭⟩) hsup𝔭
    have hcommCell' : ∀ a b : Gal(↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩)
        (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left)/↥(Ef ⟨𝔭, h𝔭⟩)), a * b = b * a :=
      fun a b => IsMulCommutative.is_comm.comm a b
    obtain ⟨𝔓, h𝔓lies, h𝔓frob, h𝔓norm⟩ :=
      NK.CFTLib.ARLAlt.exists_primeIdeal_isFrobAt_one (Ef ⟨𝔭, h𝔭⟩) 𝔭 (hEfsplit ⟨𝔭, h𝔭⟩)
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
        exact hq (isUnramified_cellAtAux (K := K) (L := L) M (Ef ⟨𝔭, h𝔭⟩)
          hsup𝔭 q hM)
      have h2 : ((m * M : ℕ) : 𝓞 ↥(Ef ⟨𝔭, h𝔭⟩)) ∈ q.asIdeal := by
        rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ hM
      exact h2
    letI : Algebra ↥(Ef ⟨𝔭, h𝔭⟩) ↥E := algOfLe (Ef ⟨𝔭, h𝔭⟩) E hle𝔭
    letI : IsScalarTower K ↥(Ef ⟨𝔭, h𝔭⟩) ↥E :=
      isScalarTower_algOfLe (Ef ⟨𝔭, h𝔭⟩) E hle𝔭
    letI : FiniteDimensional ↥(Ef ⟨𝔭, h𝔭⟩) ↥E :=
      finiteDimensional_algOfLe (Ef ⟨𝔭, h𝔭⟩) E hle𝔭
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
    have hcop𝔘 : NK.CFTLib.ArtinReciprocityIdeal.FracCoprime (K := ↥(Ef ⟨𝔭, h𝔭⟩)) 𝔪 𝔘 := by
      rw [← NK.CFTLib.ArtinReciprocityIdeal.mem_idealCoprimeGroup_iff]
      rw [h𝔘def]
      refine Subgroup.mul_mem _ (Subgroup.zpow_mem _ ?_ _) (Subgroup.zpow_mem _ ?_ _)
      · exact Subgroup.subset_closure ⟨𝔓, h𝔪𝔓, rfl⟩
      · exact (NK.CFTLib.ArtinReciprocityIdeal.mem_idealCoprimeGroup_iff 𝔪 𝔠).mpr hcop𝔠
    -- `N_{E𝔭/K}𝔘 = X 𝔭`
    have hN𝔘 : NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef ⟨𝔭, h𝔭⟩)) 𝔘 = Xa 𝔭 := by
      have h1 : NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef ⟨𝔭, h𝔭⟩))
          (NK.CFTLib.ARL.primeUnit 𝔓) = NK.CFTLib.ARL.primeUnit 𝔭 := by
        rw [NK.CFTLib.ARL.relNormUnit_primeUnit]
        apply Units.ext
        rw [Units.val_mk0, NK.CFTLib.ARL.primeUnit_val, h𝔓norm]
      have h2 : NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef ⟨𝔭, h𝔭⟩)) 𝔠 = 𝔟 := by
        rw [h𝔠def, h𝔟def]
        exact NK.CFTLib.ARL.relNormUnit_trans (K := K) (E := ↥(Ef ⟨𝔭, h𝔭⟩)) (M := ↥E)
          (𝔅 : (FractionalIdeal (𝓞 ↥E)⁰ ↥E)ˣ)
      show NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef ⟨𝔭, h𝔭⟩)) 𝔘 =
        (NK.CFTLib.ARL.primeUnit 𝔭) ^ (NK.CFTLib.Arl.exps Afr) 𝔭 *
          𝔟 ^ (-((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭))
      rw [h𝔘def, map_mul, map_zpow, map_zpow, h1, h2]
    -- `ψ_{LΩ/K}(X 𝔭) = 1`
    have hXsym : NK.CFTLib.Arl.artinSym (K := K) (L := ↥LΩ) hcommΩ'
        (Xa 𝔭 : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
      have h1 : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥LΩ) hcommΩ'
          (Xa 𝔭) = σ ^ ((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭) *
            σ ^ (-((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭)) := by
        have hp : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥LΩ) hcommΩ'
            (NK.CFTLib.ARL.primeUnit 𝔭) = σ ^ (sEx 𝔭) := by
          rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
            NK.CFTLib.ARL.primeUnit_val,
            NK.CFTLib.Arl.artinSym_prime (K := K) (L := ↥LΩ) hcommΩ' 𝔭, hsEx 𝔭 h𝔭]
        have hb : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥LΩ) hcommΩ'
            𝔟 = σ := by
          rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply, h𝔟sym]
        show NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥LΩ) hcommΩ'
          ((NK.CFTLib.ARL.primeUnit 𝔭) ^ (NK.CFTLib.Arl.exps Afr) 𝔭 *
            𝔟 ^ (-((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭))) =
          σ ^ ((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭) *
            σ ^ (-((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭))
        rw [map_mul, map_zpow, map_zpow, hp, hb, ← zpow_mul,
          mul_comm (sEx 𝔭) ((NK.CFTLib.Arl.exps Afr) 𝔭)]
      have h2 : σ ^ ((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭) *
          σ ^ (-((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭)) = 1 := by
        rw [← zpow_add, add_neg_cancel, zpow_zero]
      rw [← NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply (K := K) (L := ↥LΩ) hcommΩ'
        (Xa 𝔭), h1, h2]
    -- the restriction to `LΩ` of the Artin symbol of `𝔘` is trivial
    have hρ : (AlgEquiv.restrictNormalHom (F := K) (K₁ := CyclotomicField M L) ↥LΩ)
        (AlgEquiv.restrictScalars K (NK.CFTLib.Arl.artinSym (K := ↥(Ef ⟨𝔭, h𝔭⟩))
          (L := CyclotomicField M L) hcomm𝔭'
          (𝔘 : FractionalIdeal (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))⁰ ↥(Ef ⟨𝔭, h𝔭⟩)))) = 1 := by
      have h := artinSym_restrict_relNorm' (K := K) (M := CyclotomicField M L)
        (Ef ⟨𝔭, h𝔭⟩) LΩ hcomm𝔭' hcommΩ' 𝔪 hram𝔭 hramLΩ
        (𝔘 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥(Ef ⟨𝔭, h𝔭⟩)) hcop𝔘
      rw [h, hN𝔘, hXsym]
    -- hence the Artin symbol of `𝔘` in `LE𝔭/E𝔭` is trivial
    have hψ : NK.CFTLib.Arl.artinSym (K := ↥(Ef ⟨𝔭, h𝔭⟩))
        (L := ↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩) (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left))
        hcommCell' (𝔘 : FractionalIdeal (𝓞 ↥(Ef ⟨𝔭, h𝔭⟩))⁰ ↥(Ef ⟨𝔭, h𝔭⟩)) = 1 := by
      rw [← restrictNormalHom_artinSym_eq_ofLe (K := K) (L := L) M (Ef ⟨𝔭, h𝔭⟩)
        hcomm𝔭' hcommCell' 𝔪 hram𝔭 (𝔘 : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥(Ef ⟨𝔭, h𝔭⟩))
        hcop𝔘]
      exact restrictNormalHom_eq_one_of_sup (K := K) (L := L) M (Ef ⟨𝔭, h𝔭⟩) _ hρ
    -- the cell
    have hcell : 𝔘 ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay ↥(Ef ⟨𝔭, h𝔭⟩) 𝔪 ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRay ↥(Ef ⟨𝔭, h𝔭⟩)
          ↥(NK.CFTLib.ARLAlt.ofLe (Ef ⟨𝔭, h𝔭⟩) (Ef ⟨𝔭, h𝔭⟩ ⊔ LΩ) le_sup_left) 𝔪 :=
      NK.CFTLib.ARLAlt.cellAtAuxField (K := K) (L := L) M (Ef ⟨𝔭, h𝔭⟩) hsup𝔭 𝔪 h𝔪pos
        ⟨m, by rw [h𝔪def, mul_comm]⟩ hcellunr 𝔘 hcop𝔘 hψ
    -- descent to `K`
    have hPR := NK.CFTLib.ARLAlt.principalRay_map_relNormUnit_le (K := K) (E := ↥(Ef ⟨𝔭, h𝔭⟩))
      𝔪 m hm h𝔪pos hmlt
    have hNR := normRay_cell_descent (K := K) (L := L) M (Ef ⟨𝔭, h𝔭⟩) 𝔪 m hm hmlt
    have hmem : Xa 𝔭 ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRay K L m := by
      have hmap := Subgroup.mem_map_of_mem
        (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef ⟨𝔭, h𝔭⟩))) hcell
      rw [Subgroup.map_sup] at hmap
      rw [hN𝔘] at hmap
      exact (sup_le (le_trans hPR le_sup_left) (le_trans hNR le_sup_right)) hmap
    exact hmem
  -- ## bookkeeping
  have hXprod : ∏ 𝔭 ∈ s, Xa 𝔭 = A * 𝔟 ^ (-N) := by
    have h1 : (∏ 𝔭 ∈ s, Xa 𝔭) = (∏ 𝔭 ∈ s,
        (NK.CFTLib.ARL.primeUnit 𝔭) ^ (NK.CFTLib.Arl.exps Afr) 𝔭) *
        ∏ 𝔭 ∈ s, 𝔟 ^ (-((NK.CFTLib.Arl.exps Afr) 𝔭 * sEx 𝔭)) :=
      Finset.prod_mul_distrib
    rw [h1, ← hfac, finset_prod_zpow]
    congr 1
    rw [hNdef, ← Finset.sum_neg_distrib]
  have hprodmem : ∏ 𝔭 ∈ s, Xa 𝔭 ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
      NK.CFTLib.ArtinReciprocityIdeal.normRay K L m :=
    Subgroup.prod_mem _ (fun 𝔭 h𝔭 => hXmem 𝔭 h𝔭)
  have hcop𝔟m : NK.CFTLib.ArtinReciprocityIdeal.FracCoprime m 𝔟 := fun 𝔭 hmem =>
    hcop𝔟 𝔭 (by rw [h𝔪def, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hmem)
  have hfin : Module.finrank K ↥LΩ = Module.finrank K L := by
    rw [← IsGalois.card_aut_eq_finrank K ↥LΩ, hcard]
  have hbase : 𝔟 ^ Module.finrank K L ∈ NK.CFTLib.ArtinReciprocityIdeal.normRay K L m := by
    have h := NK.Existence.ArtinLemma.pow_finrank_mem_normRay (K := K) (L := ↥LΩ) m hcop𝔟m
    rw [hfin, normRay_LImage_eq (K := K) (L := L) M m] at h
    exact h
  obtain ⟨k, hk⟩ := hdvd
  have h𝔟N : 𝔟 ^ N ∈ NK.CFTLib.ArtinReciprocityIdeal.normRay K L m := by
    rw [hk, zpow_mul, zpow_natCast]
    exact Subgroup.zpow_mem _ hbase k
  have hAeq : A = (∏ 𝔭 ∈ s, Xa 𝔭) * 𝔟 ^ N := by
    rw [hXprod]; group
  rw [hAeq]
  exact Subgroup.mul_mem _ hprodmem (Subgroup.mem_sup_right h𝔟N)

end

end NK.NUV2.ARL
