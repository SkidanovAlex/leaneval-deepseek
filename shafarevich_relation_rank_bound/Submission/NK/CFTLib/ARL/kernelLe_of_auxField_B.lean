import Mathlib
import Submission.NK.CFTLib.ARL.AuxField
import Submission.NK.CFTLib.ARL.isGalois_cyclotomicField_over_base
import Submission.NK.CFTLib.ARL.Cyclic
import Submission.NK.CFTLib.ARL.RelNormFI
import Submission.NK.CFTLib.ARL.cyclotomicCellKernelLe_B
import Submission.NK.CFTLib.ARLAlt.Setup
import Submission.NK.CFTLib.ARLAlt.CellAtAux
import Submission.NK.CFTLib.ARLAlt.AuxLocal
import Submission.NK.CFTLib.ArtinReciprocityIdeal.relNormUnit_trans
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSym_restrict_relNorm
import Submission.NK.CFTLib.ArtinReciprocityIdeal.norm_principalRay_le
import Submission.NK.CFTLib.ArtinReciprocityIdeal.normRayLeKer
import Submission.NK.CFTLib.ArtinReciprocityIdeal.mem_idealCoprimeGroup_iff
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSymSurjectiveOnCoprime
import Submission.NK.CFTLib.ArtinReciprocityIdeal.indexPrincipalRaySupNormRayLe
import Submission.NK.Chebotarev.IsFrobAtPrimeAlgEquivSameBase
import Submission.NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension
import Submission.NK.ReconstructField.localDegree_primeTransport
import Submission.NK.CFTLib.ArtinReciprocityIdeal.CyclotomicSubextension
import Submission.NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one

/-!
# The transfer (Lang X §2, Theorem 2) from the auxiliary-field hypothesis

`NK.CFTLib.ARL.kernelLe_of_auxField_B` (this file) deduces
`ker ψ ∩ I(m) ⊆ P(m)·𝔑(m)` for a cyclic extension `L/K` from the auxiliary-field
hypothesis `NK.CFTLib.ARL.AuxFieldHyp K L m` (Artin's lemma).

The auxiliary data of `haux` at a finite set `s` of primes is a modulus `M`, a field
`E ⊆ Ω = L(ζ_M)` with `E ∩ L = K` and, for every `𝔭 ∈ s`, a subfield `E𝔭 ≤ E` with
`E𝔭·ℚ(ζ_M) = Ω` and `𝔭` splitting completely in `E𝔭/K`.

The transfer argument (Childress, *CFT*, Prop. 2.2; Lang, *ANT* X §2): factor
`A = ∏_{𝔭 ∈ s} 𝔭^{e𝔭}`; choose `𝔟 = N_{E/K}(𝔅) ∈ I(m)` with `ψ(𝔟) = σ` (surjectivity of the
Artin symbol for `Ω/E` together with the norm/restriction compatibility); for each `𝔭`,
`X𝔭 := 𝔭^{e𝔭}𝔟^{-e𝔭s𝔭}` is a norm from `E𝔭` and is killed by the cell Artin symbol
`ψ_{E𝔭·L/E𝔭}`, so the cyclotomic cell `cellAtAuxField` puts it in `P(m)·𝔑(m)`.  Multiplying and
using `n ∣ ∑ e𝔭 s𝔭` together with `𝔟^n = N_{L/K}(𝔟𝒪_L) ∈ 𝔑(m)` gives the claim.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors IsMulCommutative

noncomputable section

namespace NK.CFTLib.ARL

section FrobeniusRestriction

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **Restriction of a Frobenius element.**  Let `L/K` be a finite Galois extension of number
fields, `M` an intermediate field which is normal over `K`, and `p` a prime of `K` which is
unramified in `L`.  Then the restriction to `M` of the chosen Frobenius element at `p` in `L/K`
agrees with the chosen Frobenius element at `p` in `M/K`.  (Copied from
`Submission/Work/CFTLib/Arl/artinSym_spanSingleton_eq_one_of_ramified_congruence_by_cyclic.lean`,
which is currently not compiling; the statement and proof are unchanged.) -/
theorem restrictNormalHom_frobAtPrime_of_unramified_aux
    (M : IntermediateField K L) [FiniteDimensional K M] [Normal K M]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (hcommM : ∀ a b : Gal(↥M/K), a * b = b * a)
    (p : NK.Chebotarev.PrimeIdeal K)
    (hunr : ∀ P : NK.Chebotarev.PrimeIdeal L, P.asIdeal.LiesOver p.asIdeal →
      P.asIdeal.ramificationIdx (𝓞 K) = 1) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M
        (NK.Chebotarev.frobAtPrime (K := K) (L := L) p)
      = NK.Chebotarev.frobAtPrime (K := K) (L := ↥M) p := by
  classical
  obtain ⟨σ, hσ, huniq⟩ :=
    NK.Chebotarev.ExistsUniqueIsFrobAtPrime hcomm p hunr
  have hσeq : NK.Chebotarev.frobAtPrime (K := K) (L := L) p = σ :=
    huniq _ (NK.Chebotarev.isFrobAtPrime_frobAtPrime hcomm p hunr)
  have hunrM : ∀ Q : NK.Chebotarev.PrimeIdeal ↥M, Q.asIdeal.LiesOver p.asIdeal →
      Q.asIdeal.ramificationIdx (𝓞 K) = 1 := by
    intro Q hQ
    obtain ⟨P, hP⟩ :=
      Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
        (K := ↥M) (L := L) Q
    haveI := hP
    haveI := hQ
    have h1 : P.asIdeal.ramificationIdx (𝓞 K) = 1 :=
      hunr P (Ideal.LiesOver.trans (𝔓 := P.asIdeal) (P := Q.asIdeal) (p := p.asIdeal))
    have h2 : Q.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.ramificationIdx (𝓞 ↥M) = 1 := by
      rw [← Ideal.ramificationIdx_tower (q := Q.asIdeal) (r := P.asIdeal)]
      exact h1
    exact Nat.eq_one_of_mul_eq_one_right h2
  obtain ⟨τ, hτ, huniqM⟩ := NK.Chebotarev.ExistsUniqueIsFrobAtPrime hcommM p hunrM
  have hτeq : NK.Chebotarev.frobAtPrime (K := K) (L := ↥M) p = τ :=
    huniqM _ (NK.Chebotarev.isFrobAtPrime_frobAtPrime hcommM p hunrM)
  obtain ⟨P, hP, hPfrob⟩ := hσ
  have h2 : NK.Chebotarev.IsFrobAt (K := K) (L := ↥M)
      (P.under (𝓞 ↥M)) ((AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M) σ) :=
    NK.Chebotarev.IsFrobAtRestrictNormalHom (K := K) (M := L) M hP hPfrob
  have hlies : (P.under (𝓞 ↥M)).asIdeal.LiesOver p.asIdeal := by
    rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
    refine Ideal.LiesOver.mk ?_
    rw [Ideal.under_under]
    exact Ideal.LiesOver.over (A := 𝓞 K) (B := 𝓞 L) (P := P.asIdeal) (p := p.asIdeal)
  have h3 : NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥M) p
      ((AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M) σ) :=
    ⟨P.under (𝓞 ↥M), hlies, h2⟩
  rw [hσeq, hτeq]
  exact huniqM _ h3

end FrobeniusRestriction

/-- **Functoriality of the ideal-theoretic Artin symbol under restriction to a normal
intermediate field.**  For a finite Galois extension `M/k` of number fields and a normal
intermediate field `T`, the restriction to `T` of the Artin symbol of an ideal coprime to a modulus
`mm` that contains all the ramified primes is the Artin symbol of the same ideal in `T/k`. -/
theorem artinSym_restrictNormalHom {k M : Type} [Field k] [NumberField k] [Field M]
    [NumberField M] [Algebra k M] [FiniteDimensional k M] [IsGalois k M]
    (T : IntermediateField k M) [FiniteDimensional k ↥T] [NumberField ↥T] [Normal k ↥T]
    (hcomm : ∀ a b : Gal(M/k), a * b = b * a)
    (hcommT : ∀ a b : Gal(↥T/k), a * b = b * a)
    (mm : ℕ)
    (hram : ∀ p : NK.Chebotarev.PrimeIdeal k,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := k) (L := M) p →
      (mm : NumberField.RingOfIntegers k) ∈ p.asIdeal)
    (A : NK.CFTLib.ArtinReciprocityIdeal.Frac k)
    (hcop : NK.CFTLib.ArtinReciprocityIdeal.FracCoprime mm A) :
    AlgEquiv.restrictNormalHom (F := k) (K₁ := M) ↥T
        (NK.CFTLib.Arl.artinSym (K := k) (L := M) hcomm
          (A : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers k)) k))
      = NK.CFTLib.Arl.artinSym (K := k) (L := ↥T) hcommT
          (A : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers k)) k) := by
  classical
  letI galM : CommMonoid Gal(M/k) := NK.CFTLib.Arl.galCommMonoid hcomm
  letI galT : CommMonoid Gal(↥T/k) := NK.CFTLib.Arl.galCommMonoid hcommT
  have hA : NK.CFTLib.Arl.artinSym (K := k) (L := M) hcomm
      (A : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers k)) k)
      = (NK.CFTLib.Arl.exps
          (A : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers k)) k)).prod
          (fun 𝔭 (e : ℤ) => (NK.Chebotarev.frobAtPrime (K := k) (L := M) 𝔭) ^ e) := rfl
  have hB : NK.CFTLib.Arl.artinSym (K := k) (L := ↥T) hcommT
      (A : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers k)) k)
      = (NK.CFTLib.Arl.exps
          (A : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers k)) k)).prod
          (fun 𝔭 (e : ℤ) => (NK.Chebotarev.frobAtPrime (K := k) (L := ↥T) 𝔭) ^ e) := rfl
  have hterm : ∀ 𝔭 ∈ (NK.CFTLib.Arl.exps
        (A : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers k)) k)).support,
      AlgEquiv.restrictNormalHom (F := k) (K₁ := M) ↥T
        (NK.Chebotarev.frobAtPrime (K := k) (L := M) 𝔭)
      = NK.Chebotarev.frobAtPrime (K := k) (L := ↥T) 𝔭 := by
    intro 𝔭 h𝔭
    refine restrictNormalHom_frobAtPrime_of_unramified_aux T hcomm hcommT 𝔭 ?_
    by_contra hunr
    have hmm : (mm : NumberField.RingOfIntegers k) ∈ 𝔭.asIdeal := hram 𝔭 hunr
    have hcount : FractionalIdeal.count k 𝔭
        (A : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers k)) k) ≠ 0 := by
      have h := Finsupp.mem_support_iff.mp h𝔭
      rwa [NK.CFTLib.Arl.exps_apply] at h
    exact hcount (hcop 𝔭 hmm)
  rw [hA, hB]
  rw [Finsupp.prod_of_support_subset _ (le_refl _)
      (fun 𝔭 (e : ℤ) => (NK.Chebotarev.frobAtPrime (K := k) (L := M) 𝔭) ^ e)
      (fun i _ => zpow_zero _)]
  rw [Finsupp.prod_of_support_subset _ (le_refl _)
      (fun 𝔭 (e : ℤ) => (NK.Chebotarev.frobAtPrime (K := k) (L := ↥T) 𝔭) ^ e)
      (fun i _ => zpow_zero _)]
  rw [map_prod]
  exact Finset.prod_congr rfl fun 𝔭 h𝔭 => by rw [map_zpow, hterm 𝔭 h𝔭]

/-- **Functoriality of the Artin symbol under relative norms** — the statement of
`NK.CFTLib.ArtinReciprocityIdeal.artinSym_restrict_relNorm` with the (unused) join and meet
hypotheses `E ⊔ L = ⊤` and `E ⊓ L = ⊥` deleted.  The proof is that of the cited theorem. -/
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
  -- the two sides are monoid homomorphisms of the group of fractional ideals of `↥E`
  let Φ : (M ≃ₐ[↥E] M) →* (↥L ≃ₐ[K] ↥L) :=
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L).comp (AlgEquiv.restrictScalarsHom K)
  let F : NK.CFTLib.ArtinReciprocityIdeal.Frac ↥E →* (↥L ≃ₐ[K] ↥L) := Φ.comp (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := ↥E) (L := M) hcommE)
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
    -- at a prime in the support both sides are computed by the prime case
    have hprime : ∀ 𝔮 ∈ S, F (NK.CFTLib.ARL.primeUnit 𝔮)
        = G (NK.CFTLib.ARL.primeUnit 𝔮) := by
      intro 𝔮 h𝔮
      have hcount : FractionalIdeal.count ↥E 𝔮 (𝔄 : FractionalIdeal (𝓞 ↥E)⁰ ↥E) ≠ 0 :=
        (hSmem 𝔮).mp h𝔮
      have hunrE : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E) (L := M) 𝔮 := by
        by_contra h
        exact hcount (hcop 𝔮 (hramE 𝔮 h))
      have hunrL : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥L) (𝔮.under (𝓞 K)) := by
        by_contra h
        have hm : (m : 𝓞 K) ∈ (𝔮.under (𝓞 K)).asIdeal := hram (𝔮.under (𝓞 K)) h
        rw [HeightOneSpectrum.under_asIdeal] at hm
        have hm' : (m : 𝓞 ↥E) ∈ 𝔮.asIdeal := by
          have h2 := (Ideal.mem_under (𝓞 K) 𝔮.asIdeal).mp hm
          simpa using h2
        exact hcount (hcop 𝔮 hm')
      have hF : F (NK.CFTLib.ARL.primeUnit 𝔮) = AlgEquiv.restrictNormalHom (F := K)
          (K₁ := M) L
          ((NK.Chebotarev.frobAtPrime (K := ↥E) (L := M) 𝔮).restrictScalars K) := by
        change Φ (NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := ↥E) (L := M) hcommE
          (NK.CFTLib.ARL.primeUnit 𝔮)) = _
        rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply, NK.CFTLib.ARL.primeUnit_val,
          NK.CFTLib.Arl.artinSym_prime]
        rfl
      have hG : G (NK.CFTLib.ARL.primeUnit 𝔮) = (NK.Chebotarev.frobAtPrime (K := K)
          (L := ↥L) (𝔮.under (𝓞 K))) ^ (𝔮.asIdeal.inertiaDeg (𝓞 K)) := by
        haveI : 𝔮.asIdeal.IsMaximal :=
          Ring.DimensionLEOne.maximalOfPrime 𝔮.ne_bot 𝔮.isPrime
        have hqne : (𝔮.under (𝓞 K)).asIdeal ≠ ⊥ := by
          rw [HeightOneSpectrum.under_asIdeal]
          exact Ideal.under_ne_bot (𝓞 K) 𝔮.ne_bot
        haveI : ((𝔮.under (𝓞 K)).asIdeal).IsMaximal :=
          Ring.DimensionLEOne.maximalOfPrime hqne inferInstance
        haveI : 𝔮.asIdeal.LiesOver (𝔮.under (𝓞 K)).asIdeal :=
          ⟨HeightOneSpectrum.under_asIdeal (𝓞 K) 𝔮⟩
        change NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom (K := K) (L := ↥L) hcommL
          (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥E)
            (NK.CFTLib.ARL.primeUnit 𝔮)) = _
        rw [NK.CFTLib.ARL.relNormUnit_primeUnit, NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply, Units.val_mk0,
          Ideal.relNorm_eq_pow_of_isMaximal 𝔮.asIdeal ((𝔮.under (𝓞 K)).asIdeal),
          FractionalIdeal.coeIdeal_pow,
          NK.CFTLib.ArtinReciprocityIdeal.artinSymFrac_pow hcommL
            (FractionalIdeal.coeIdeal_ne_zero.mpr ((𝔮.under (𝓞 K)).ne_bot)),
          NK.CFTLib.Arl.artinSym_prime]
      rw [hF, hG]
      exact NK.CFTLib.ArtinReciprocityIdeal.restrict_frobAtPrime_eq E L hcommE hcommL 𝔮 hunrE hunrL
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
  simpa only [F, G, Φ, MonoidHom.comp_apply, NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
    AlgEquiv.restrictScalarsHom_apply] using hFG
/-! ## Auxiliary transport and ramification lemmas -/

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

/-- **The cell `E·L` of the transfer is unramified over `E` at the primes not dividing the
cyclotomic level `M`.**  This is the ramification input of the cyclotomic cell
`NK.CFTLib.ARLAlt.cellAtAuxField`: `Ω = E(ζ_M)` is cyclotomic of level `M` over `E`
(`NK.CFTLib.ARLAlt.isCyclotomicExtension_of_sup_adjoin_zeta`), hence unramified at `q` for
`M ∉ q` (`NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension`), and the subextension `E·L` of `Ω`
inherits this (multiplicativity of the ramification index in towers). -/
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

/-- **`L`, viewed inside `Ω = L(ζ_M)`, is unramified at `p` over `K` whenever `p` is prime to
`(m·M)`**, where `m` is a modulus containing all the ramified primes of `L/K`.

Indeed `Ω` is unramified at `p` over `K`: the tower `K ⊆ L ⊆ Ω` exhibits
`e(𝔓/𝔭) = e(𝔮/𝔭)·e(𝔓/𝔮)` with `e(𝔮/𝔭) = 1` (the hypothesis `hram`, `𝔭 ∤ (m)`) and
`e(𝔓/𝔮) = 1` (`Ω/L` is cyclotomic of level `M`, `𝔮 ∤ (M)`).  The subextension `L ⊆ Ω` then
inherits this by the tower `K ⊆ L ⊆ Ω`. -/
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
  -- the unramifiedness of `Ω/K` at `p`
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
  -- extend `P'` to `Ω` and use the tower
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

/-! ## The algebra structure on `↥B` induced by an inclusion `A ≤ B` of intermediate fields

Mathlib provides no `Algebra ↥A ↥B` instance for intermediate fields `A ≤ B` of a common
extension (the missing structure in the transfer, where one needs the tower `K ⊆ L ⊆ E·L ⊆ Ω`).
We provide it here, together with the two facts the transfer needs: the scalar towers over `K`
and over `ℚ`, and finite-dimensionality. -/

/-- **The `K`-algebra structure on `↥B` induced by the inclusion `↥A → ↥B`** for intermediate
fields `A ≤ B`. -/
noncomputable def algOfLe {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (A B : IntermediateField K Ω) (h : A ≤ B) : Algebra ↥A ↥B :=
  RingHom.toAlgebra ((IntermediateField.inclusion h).toRingHom)

/-- The algebra map of `algOfLe` is the inclusion of intermediate fields. -/
lemma algOfLe_algebraMap_apply {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (A B : IntermediateField K Ω) (h : A ≤ B) (x : ↥A) :
    (@algebraMap ↥A ↥B _ _ (algOfLe A B h)) x = (IntermediateField.inclusion h) x := rfl

/-- **The scalar tower `K → ↥A → ↥B`** for the algebra structure `algOfLe`. -/
lemma isScalarTower_algOfLe {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (A B : IntermediateField K Ω) (h : A ≤ B) :
    letI := algOfLe A B h
    IsScalarTower K ↥A ↥B := by
  letI := algOfLe A B h
  refine ⟨fun x a b => ?_⟩
  have h1 : (@algebraMap ↥A ↥B _ _ (algOfLe A B h)) (algebraMap K ↥A x) =
      (algebraMap K ↥B x : ↥B) := by
    apply Subtype.ext
    show ((IntermediateField.inclusion h) (algebraMap K ↥A x) : Ω) = _
    rw [IntermediateField.coe_inclusion, IntermediateField.coe_algebraMap_apply,
      IntermediateField.coe_algebraMap_apply]
  simp only [Algebra.smul_def, map_mul, h1]
  ring

/-- **`↥B` is finite-dimensional over `↥A`** for intermediate fields `A ≤ B` of a finite
extension, with the algebra structure `algOfLe`. -/
lemma finiteDimensional_algOfLe {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (A B : IntermediateField K Ω) [FiniteDimensional K ↥B] (h : A ≤ B) :
    letI := algOfLe A B h
    FiniteDimensional ↥A ↥B := by
  letI := algOfLe A B h
  haveI hT : IsScalarTower K ↥A ↥B := isScalarTower_algOfLe A B h
  exact Module.Finite.of_restrictScalars_finite K ↥A ↥B

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

/-- **The Galois group of the image of `L` in `L(ζ_M)` is commutative**, being isomorphic (by
conjugation along `NK.CFTLib.ARLAlt.LImageEquiv`) to a subgroup of the commutative group
`Gal(L/K)`. -/
theorem isMulCommutative_LImage {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (Gal(L/K))]
    (M : ℕ) :
    IsMulCommutative (Gal(↥(NK.CFTLib.ARLAlt.LImage (K := K) (L := L) M)/K)) := by
  have hinj : Function.Injective
      (conjHom (NK.CFTLib.ARLAlt.LImageEquiv (K := K) (L := L) M)) :=
    conjHom_injective _
  refine IsMulCommutative.of_comm (fun a b => ?_)
  exact hinj (by
    rw [map_mul, map_mul]
    exact IsMulCommutative.is_comm.comm _ _)

/-- **The transfer of Lang X §2, Theorem 2**: the auxiliary-field hypothesis of Artin's lemma
implies the kernel containment `ker ψ ∩ I(m) ⊆ P(m)·𝔑(m)`. -/
theorem kernelLe_of_auxField_B (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
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
  -- ## The factorisation of `A` over its support
  set s : Finset (NK.Chebotarev.PrimeIdeal K) :=
    (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors (K := K)
      (A : FractionalIdeal (𝓞 K)⁰ K))).toFinset with hsdef
  set e : NK.Chebotarev.PrimeIdeal K → ℤ := fun 𝔭 =>
    FractionalIdeal.count K 𝔭 (A : FractionalIdeal (𝓞 K)⁰ K) with hedef
  have hsmem : ∀ 𝔭, 𝔭 ∈ s ↔ e 𝔭 ≠ 0 := fun 𝔭 => Set.Finite.mem_toFinset _
  have hsupp : Function.mulSupport (fun 𝔭 : NK.Chebotarev.PrimeIdeal K =>
      ((𝔭.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ^ e 𝔭) ⊆ ↑s := by
    intro 𝔭 h𝔭
    exact (hsmem 𝔭).mpr fun h0 => h𝔭 (by simp only [h0, zpow_zero])
  have hfac : (∏ 𝔭 ∈ s, (NK.CFTLib.ARL.primeUnit 𝔭) ^ (e 𝔭)) = A := by
    apply Units.ext
    rw [Units.coe_prod]
    simp only [NK.CFTLib.ARL.primeUnit_val, Units.val_zpow_eq_zpow_val]
    rw [← finprod_eq_prod_of_mulSupport_subset _ hsupp]
    exact FractionalIdeal.finprod_heightOneSpectrum_factorization' K A.ne_zero
  have hs : ∀ 𝔭 ∈ s, (m : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro 𝔭 h𝔭
    intro hmem
    exact (hsmem 𝔭).mp h𝔭 (hcop 𝔭 hmem)
  -- ## Artin's lemma
  obtain ⟨M, hMne, hMcop, _hSvoid, hNormavoid, hdisjLz, E, hEdisj, hElt⟩ :=
    haux s hs ∅ (by simp)
  -- ## The trivial case `s = ∅`
  rcases s.eq_empty_or_nonempty with hsempty | ⟨𝔭₀, h𝔭₀⟩
  · rw [← hfac, hsempty, Finset.prod_empty]
    exact Subgroup.one_mem _
  · sorry

/-! ## The transfer: Galois-theoretic foundations

The auxiliary fields of `NK.CFTLib.ARL.AuxFieldHyp` live in the cyclotomic field
`Ω = L(ζ_M)`.  The transfer argument needs two Galois-theoretic facts about `Ω/K`:

* `Gal(Ω/K)` is commutative (a compositum of two abelian extensions), hence *every* intermediate
  field is Galois over `K`;
* the restriction `Gal(Ω/E) → Gal(L/K)` (for `E ⊓ L = K`) is surjective.

These are the lemmas `mul_comm_cyclotomicField` and
`restrictNormalHom_comp_restrictScalars_surjective` below. -/

/-- A group admitting an injective homomorphism into a commutative monoid is commutative. -/
lemma mul_comm_of_injective {G : Type*} [Group G] {H : Type*} [Monoid H] [IsMulCommutative H]
    (f : G →* H) (hf : Function.Injective f) (a b : G) : a * b = b * a := by
  apply hf
  rw [map_mul, map_mul, IsMulCommutative.is_comm.comm]

/-- **`CyclotomicField M L` is `L` adjoined with a primitive `M`-th root of unity.** -/
theorem adjoin_zeta_eq_top_aux (K L : Type) [Field K] [Field L] [CharZero L] [Algebra K L]
    (M : ℕ) [NeZero M] :
    (⊤ : IntermediateField L (CyclotomicField M L)) =
      IntermediateField.adjoin L
        ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
          Set (CyclotomicField M L)) := by
  haveI htop : IsCyclotomicExtension {M} L
      ↥(⊤ : IntermediateField L (CyclotomicField M L)) :=
    IsCyclotomicExtension.equiv {M} L (CyclotomicField M L)
      (IntermediateField.topEquiv (F := L)).symm
  exact (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin M L
    (CyclotomicField M L) ⊤ (IsCyclotomicExtension.zeta_spec M L _)).mp htop

/-- **`L(ζ_M) = L ⊔ K(ζ_M)`** as intermediate fields of `CyclotomicField M L` over `K`. -/
theorem sup_restrictScalars_adjoin_zeta_eq_top_aux {K L : Type} [Field K] [Field L]
    [CharZero L] [Algebra K L] (M : ℕ) [NeZero M] :
    (⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K ⊔
      IntermediateField.adjoin K
        ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
          Set (CyclotomicField M L)) = ⊤ := by
  set A : IntermediateField K (CyclotomicField M L) :=
    (⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K with hA
  set ζ := IsCyclotomicExtension.zeta M L (CyclotomicField M L) with hζ
  set B : IntermediateField K (CyclotomicField M L) :=
    IntermediateField.adjoin K ({ζ} : Set (CyclotomicField M L)) with hB
  have htop : (⊤ : IntermediateField L (CyclotomicField M L)) =
      IntermediateField.adjoin L ({ζ} : Set (CyclotomicField M L)) :=
    adjoin_zeta_eq_top_aux K L M
  have hsub : (IntermediateField.adjoin L ({ζ} : Set (CyclotomicField M L)) :
      Set (CyclotomicField M L)) ⊆
      (IntermediateField.adjoin K
        ((A ⊔ B : IntermediateField K (CyclotomicField M L)) :
          Set (CyclotomicField M L))) := by
    rw [IntermediateField.adjoin_subset_adjoin_iff]
    constructor
    · rintro y ⟨l, rfl⟩
      refine IntermediateField.subset_adjoin K _ ((le_sup_left : A ≤ A ⊔ B) ?_)
      rw [hA]
      exact (IntermediateField.mem_restrictScalars K).mpr (IntermediateField.mem_bot.mpr ⟨l, rfl⟩)
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact IntermediateField.subset_adjoin K _
        ((le_sup_right : B ≤ A ⊔ B)
          (IntermediateField.subset_adjoin K _ (Set.mem_singleton ζ)))
  have hle : IntermediateField.adjoin K
      ((A ⊔ B : IntermediateField K (CyclotomicField M L)) :
        Set (CyclotomicField M L)) ≤ A ⊔ B :=
    IntermediateField.adjoin_le_iff.mpr (fun x hx => hx)
  have huniv : (IntermediateField.adjoin L ({ζ} : Set (CyclotomicField M L)) :
      Set (CyclotomicField M L)) = Set.univ := by
    rw [← htop]
    rfl
  change A ⊔ B = ⊤
  refine le_antisymm le_top ?_
  intro x hx
  exact hle (hsub (huniv ▸ Set.mem_univ x))

/-- **The Galois group of `L(ζ_M)` over `K` is commutative** whenever `Gal(L/K)` is: it injects
into `Gal(L/K) × Gal(K(ζ_M)/K)`, and both factors are commutative (the second through the
cyclotomic character). -/
theorem mul_comm_cyclotomicField {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcommL : ∀ a b : Gal(L/K), a * b = b * a)
    (M : ℕ) [NeZero M] :
    ∀ a b : Gal(CyclotomicField M L / K), a * b = b * a := by
  intro a b
  set Ω := CyclotomicField M L
  set A : IntermediateField K Ω := (⊥ : IntermediateField L Ω).restrictScalars K with hA
  set ζ : Ω := IsCyclotomicExtension.zeta M L Ω with hζdef
  set B : IntermediateField K Ω := IntermediateField.adjoin K ({ζ} : Set Ω) with hB
  have hζ : IsPrimitiveRoot ζ M := IsCyclotomicExtension.zeta_spec M L Ω
  have htop : A ⊔ B = ⊤ := by
    simpa only [hA, hB, hζdef] using sup_restrictScalars_adjoin_zeta_eq_top_aux (K := K) (L := L) M
  haveI hAgal : IsGalois K ↥A :=
    IsGalois.of_algEquiv ((IntermediateField.botEquiv L Ω).symm.restrictScalars K)
  have hAc : ∀ a b : Gal(↥A/K), a * b = b * a := by
    intro a b
    have e : Gal(L/K) ≃* Gal(↥A/K) :=
      AlgEquiv.autCongr ((IntermediateField.botEquiv L Ω).symm.restrictScalars K)
    refine e.symm.injective ?_
    rw [map_mul, map_mul, hcommL]
  haveI : IsMulCommutative Gal(↥A/K) := IsMulCommutative.of_comm hAc
  haveI hBcyc : IsCyclotomicExtension {M} K ↥B :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin M K Ω B hζ).mpr rfl
  haveI hBgal : IsGalois K ↥B := IsCyclotomicExtension.isGalois {M} K ↥B
  haveI : IsMulCommutative Gal(↥B/K) := by
    refine IsMulCommutative.of_comm (fun a b => ?_)
    exact mul_comm_of_injective
      (IsPrimitiveRoot.autToPow K (IsCyclotomicExtension.zeta_spec M K ↥B))
      (IsPrimitiveRoot.autToPow_injective K (IsCyclotomicExtension.zeta_spec M K ↥B)) a b
  haveI : Normal K ↥A := inferInstance
  haveI : Normal K ↥B := inferInstance
  set φ : Gal(Ω/K) →* Gal(↥A/K) × Gal(↥B/K) :=
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) ↥A).prod
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) ↥B) with hφ
  have hφinj : Function.Injective φ := by
    intro σ τ hστ
    have hker : φ (σ * τ⁻¹) = 1 := by rw [map_mul, hστ, map_inv, mul_inv_cancel]
    have h1 : A ≤ IntermediateField.fixedField
        (Subgroup.zpowers (AlgEquiv.restrictScalars K (σ * τ⁻¹))) := by
      rw [IntermediateField.le_iff_le, Subgroup.zpowers_le, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hc := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars K (σ * τ⁻¹)) ↥A ⟨x, hx⟩
      have h2 : (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) ↥A) (σ * τ⁻¹) = 1 := by
        have := congrArg Prod.fst hker
        simpa [hφ] using this
      rw [show (AlgEquiv.restrictScalars K (σ * τ⁻¹)).restrictNormal ↥A = 1 from h2] at hc
      simpa using hc.symm
    have h2 : B ≤ IntermediateField.fixedField
        (Subgroup.zpowers (AlgEquiv.restrictScalars K (σ * τ⁻¹))) := by
      rw [IntermediateField.le_iff_le, Subgroup.zpowers_le, IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hc := AlgEquiv.restrictNormal_commutes (AlgEquiv.restrictScalars K (σ * τ⁻¹)) ↥B ⟨x, hx⟩
      have h3 : (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) ↥B) (σ * τ⁻¹) = 1 := by
        have := congrArg Prod.snd hker
        simpa [hφ] using this
      rw [show (AlgEquiv.restrictScalars K (σ * τ⁻¹)).restrictNormal ↥B = 1 from h3] at hc
      simpa using hc.symm
    have htop' : (⊤ : IntermediateField K Ω) ≤ IntermediateField.fixedField
        (Subgroup.zpowers (AlgEquiv.restrictScalars K (σ * τ⁻¹))) := by
      rw [← htop]
      exact sup_le h1 h2
    have hfix : ∀ x : Ω, (AlgEquiv.restrictScalars K (σ * τ⁻¹)) x = x := by
      intro x
      have hx : x ∈ IntermediateField.fixedField
          (Subgroup.zpowers (AlgEquiv.restrictScalars K (σ * τ⁻¹))) :=
        htop' (IntermediateField.mem_top)
      rw [IntermediateField.mem_fixedField_iff] at hx
      exact hx _ (Subgroup.mem_zpowers _)
    have : (σ * τ⁻¹ : Gal(Ω/K)) = 1 := by
      ext x
      exact hfix x
    exact mul_inv_eq_one.mp this
  have hfin : φ (a * b) = φ (b * a) := by
    rw [map_mul, map_mul, IsMulCommutative.is_comm.comm]
  exact hφinj hfin

/-- **In a finite Galois extension with commutative Galois group every intermediate field is
Galois over the base.** -/
theorem isGalois_intermediateField_of_comm {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]
    [FiniteDimensional F Ω] [IsGalois F Ω] [IsMulCommutative Gal(Ω/F)]
    (F' : IntermediateField F Ω) : IsGalois F ↥F' := by
  haveI hN : (F'.fixingSubgroup).Normal := Subgroup.normal_of_isMulCommutative _
  have h : IntermediateField.fixedField F'.fixingSubgroup = F' :=
    IsGalois.fixedField_fixingSubgroup F'
  rw [← h]
  exact IsGalois.of_fixedField_normal_subgroup F'.fixingSubgroup

/-- **Every intermediate field of `L(ζ_M)/K` is Galois over `K`** when `Gal(L/K)` is commutative:
the Galois group `Gal(L(ζ_M)/K)` is commutative by `mul_comm_cyclotomicField`. -/
theorem isGalois_intermediateField_cyclotomicField_aux {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcommL : ∀ a b : Gal(L/K), a * b = b * a) (M : ℕ) [NeZero M]
    (F : IntermediateField K (CyclotomicField M L)) : IsGalois K ↥F := by
  haveI hgal : IsGalois K (CyclotomicField M L) :=
    NK.CFTLib.ARL.isGalois_cyclotomicField_over_base (K := K) (L := L) M
  haveI : IsMulCommutative Gal(CyclotomicField M L / K) :=
    IsMulCommutative.of_comm (mul_comm_cyclotomicField hcommL M)
  exact isGalois_intermediateField_of_comm F

/-- **The restriction `Gal(Ω/E) → Gal(L/K)` is surjective** when `E ⊓ L = ⊥` (inside an ambient
Galois extension `Ω/K`).  This is what lifts an element of `Gal(L/K)` to `Gal(Ω/E)`; the proof
decomposes `Gal(Ω/K) = Gal(Ω/E)·Gal(Ω/L)` using the Galois correspondence (the fixed field of a
subgroup is the intersection of its fixed fields). -/
lemma restrictNormalHom_comp_restrictScalars_surjective {K Ω : Type} [Field K] [NumberField K]
    [Field Ω] [NumberField Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    (E L : IntermediateField K Ω) [FiniteDimensional K ↥E] [NumberField ↥E]
    [FiniteDimensional K ↥L] [NumberField ↥L] [IsGalois K ↥L] [IsGalois K ↥E]
    (hdisj : E ⊓ L = ⊥) :
    Function.Surjective
      ((AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) ↥L).comp
        (NK.CFTLib.Arl.restrictScalarsHom E)) := by
  classical
  set r : Gal(Ω/K) →* Gal(↥L/K) :=
    AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) ↥L with hr
  -- ## the two fixing subgroups join to everything
  have htop : E.fixingSubgroup ⊔ L.fixingSubgroup = ⊤ := by
    have hfixE : IntermediateField.fixedField E.fixingSubgroup = E :=
      IsGalois.fixedField_fixingSubgroup E
    have hfixL : IntermediateField.fixedField L.fixingSubgroup = L :=
      IsGalois.fixedField_fixingSubgroup L
    have h1 : IntermediateField.fixedField (E.fixingSubgroup ⊔ L.fixingSubgroup) ≤ E :=
      (IntermediateField.fixedField_le le_sup_left).trans hfixE.le
    have h2 : IntermediateField.fixedField (E.fixingSubgroup ⊔ L.fixingSubgroup) ≤ L :=
      (IntermediateField.fixedField_le le_sup_right).trans hfixL.le
    have hle : IntermediateField.fixedField (E.fixingSubgroup ⊔ L.fixingSubgroup) ≤
        (⊥ : IntermediateField K Ω) := (le_inf h1 h2).trans hdisj.le
    have hbot : IntermediateField.fixedField (E.fixingSubgroup ⊔ L.fixingSubgroup) = ⊥ :=
      le_antisymm hle bot_le
    have h := IntermediateField.fixingSubgroup_fixedField (E.fixingSubgroup ⊔ L.fixingSubgroup)
    rw [hbot, IntermediateField.fixingSubgroup_bot] at h
    exact h.symm
  -- ## the elements of `L.fixingSubgroup` restrict to `1`
  have hBker : L.fixingSubgroup ≤ r.ker := by
    rw [hr, IntermediateField.restrictNormalHom_ker]
  -- ## the image of `E.fixingSubgroup` in `Gal(L/K)` is everything
  have hmapA : E.fixingSubgroup.map r = ⊤ := by
    have hsurj : Function.Surjective r := by
      rw [hr]
      exact AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := ↥L) Ω
    have h1 : E.fixingSubgroup.map r ⊔ L.fixingSubgroup.map r = ⊤ := by
      rw [← Subgroup.map_sup, htop]
      exact Subgroup.map_top_of_surjective r hsurj
    rwa [Subgroup.map_eq_bot_iff L.fixingSubgroup |>.mpr hBker, sup_bot_eq] at h1
  -- ## conclusion
  intro σ
  have hmem : σ ∈ E.fixingSubgroup.map r := by rw [hmapA]; exact Subgroup.mem_top σ
  obtain ⟨a, ha, haσ⟩ := Subgroup.mem_map.mp hmem
  refine ⟨(IntermediateField.fixingSubgroupEquiv E) ⟨a, ha⟩, ?_⟩
  show r ((NK.CFTLib.Arl.restrictScalarsHom E)
    ((IntermediateField.fixingSubgroupEquiv E) ⟨a, ha⟩)) = σ
  have hcast : (NK.CFTLib.Arl.restrictScalarsHom E)
      ((IntermediateField.fixingSubgroupEquiv E) ⟨a, ha⟩) = a := by
    rw [NK.CFTLib.Arl.restrictScalarsHom_apply]
    exact AlgEquiv.ext (fun x => rfl)
  rw [hcast, haσ]

end NK.CFTLib.ARL
