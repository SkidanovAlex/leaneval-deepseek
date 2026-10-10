import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Submission.NK.CFTLib.ARL.isGalois_cyclotomicField_over_base
import Submission.NK.CFTLib.ARLAlt.CellAtAux
import Submission.NK.CFTLib.ARLAlt.Descent
import Submission.NK.CFTLib.Arl.prod_frobAtPrime_ramificationIdx_eq_one
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSym_restrict_relNorm_of_normal
import Submission.NK.Existence.ArtinLemma.helpers
import Submission.NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension
import Submission.NK.ReconstructField.localDegree_primeTransport
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The transfer of Artin's lemma (Lang, *Algebraic Number Theory*, X §2, Theorem 2)

`NK.CFTLib.ARL.transfer_of_auxField` is the transfer step of the ideal-theoretic reciprocity
law for a finite **cyclic** extension `L/K` of number fields: from the auxiliary-field hypothesis
`NK.CFTLib.ARL.AuxFieldHyp K L m` (Artin's lemma, in the corrected per-prime form) and a modulus
`m` containing all primes ramified in `L/K`, it deduces the kernel containment

  `ker ψ ∩ I(m) ⊆ P(m)·𝔑(m)`,

i.e. every fractional ideal `A` coprime to `(m)` whose Artin symbol `ψ_{L/K}(A)` is trivial lies in
the product `principalRay K m ⊔ normRay K L m`.

## The proof (Childress, *Class Field Theory*, Prop. 2.2; Lang, *ANT* X §2)

Factor `A = ∏_{𝔭 ∈ s} 𝔭 ^{e𝔭}`; apply `haux` to the support `s`, obtaining `M`, `E ⊆ L(ζ_M)` with
`E ⊓ L = K` and, for every `𝔭 ∈ s`, a subfield `E𝔭 ≤ E` with `E𝔭 ⊔ ℚ(ζ_M) = L(ζ_M)` in which `𝔭`
splits completely.  With `𝔪 := m·M`:

* pick `𝔅 ∈ I(𝔪)` of `E` whose Artin symbol in `L(ζ_M)/E` restricts to a generator `σ` of
  `Gal(L(ζ_M)/K) ≅ Gal(L/K)` (surjectivity of the Artin map plus the transitivity of the
  restriction `Gal(Ω/E) ↠ Gal(L/K)` for `E ⊓ L = K`), and put `𝔟 := N_{E/K}𝔅`, so that
  `ψ_{L/K}(𝔟) = σ` by the norm/restriction compatibility `ψ_{Ω/E}(𝔄)|_L = ψ_{L/K}(N_{E/K}𝔄)`;
* for `𝔭 ∈ s`, let `𝔓𝔭` be a prime of `E𝔭` above `𝔭` (so `N_{E𝔭/K}𝔓𝔭 = 𝔭`, as `𝔭` splits
  completely), and put `𝔘𝔭 := 𝔓𝔭^{e𝔭}·(N_{E/E𝔭}𝔅)^{-e𝔭 s𝔭}`, where `σ^{s𝔭} = ψ_{L/K}(𝔭)`.  Then
  `N_{E𝔭/K}𝔘𝔭 = 𝔭^{e𝔭}𝔟^{-e𝔭s𝔭} =: X𝔭`, and `ψ(X𝔭) = 1`; by the compatibility and the injectivity
  of the restriction `Gal(E𝔭·L/E𝔭) → Gal(L/K)` this gives `ψ_{E𝔭·L/E𝔭}(𝔘𝔭) = 1`, so the
  cyclotomic cell (`NK.CFTLib.ARLAlt.cellAtAuxField`) puts `𝔘𝔭 ∈ P_{E𝔭}(𝔪)·𝔑(𝔪)`, and norm
  descent gives `X𝔭 ∈ P_K(m)·𝔑_{L/K}(m)`;
* multiplying over `𝔭 ∈ s` and using `[L:K] ∣ Σ e𝔭 s𝔭` (from `ψ_{L/K}(A) = 1`) together with
  `𝔟^{[L:K]} = N_{L/K}(𝔟·𝒪_L) ∈ 𝔑(m)` concludes the proof.

## Contents of this file

The file is self-contained apart from the *stable* library modules it imports (the `ARLAlt`
development, `RelNormFI`, `CyclotomicSubextension`, the Artin-symbol/norm-ray lemmas of
`NK.CFTLib.ArtinReciprocityIdeal`, the cyclotomic unramifiedness of
`NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension`, and
`NK.Existence.ArtinLemma.pow_finrank_mem_normRay`):

* `NK.CFTLib.ARL.TFH` — the helper lemmas of the transfer (Frobenius restriction, the
  conjugation of Galois groups, base change `algOfLe`, ramification bookkeeping
  `isUnramified_LImage`/`isUnramified_cellAtAux`, the surjectivity
  `Gal(Ω/E) ↠ Gal(L/K)` for `E ⊓ L = K`, ...);
* `NK.CFTLib.ARL.TFP.transferAux` — the transfer itself (the statement of the target lemma);
* `NK.CFTLib.ARL.transfer_of_auxField` — the requested lemma, from `transferAux`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors IsMulCommutative

noncomputable section

namespace NK.CFTLib.ARL.TFH
open NK.CFTLib.ARL

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


end NK.CFTLib.ARL.TFH

namespace NK.CFTLib.ARL.TFP
open NK.CFTLib.ArtinReciprocityIdeal


/-! ## Auxiliary lemmas for the transfer step of Artin's trick -/



/-- `FracCoprime` is multiplicative. -/
lemma FracCoprime_mul {K : Type} [Field K] [NumberField K] {m : ℕ} {A B : Frac K}
    (hA : FracCoprime m A) (hB : FracCoprime m B) : FracCoprime m (A * B) := by
  intro 𝔭 h𝔭
  rw [Units.val_mul, FractionalIdeal.count_mul K 𝔭 (Units.ne_zero A) (Units.ne_zero B),
    hA 𝔭 h𝔭, hB 𝔭 h𝔭, add_zero]

/-- `FracCoprime` is preserved by integer powers. -/
lemma FracCoprime_zpow {K : Type} [Field K] [NumberField K] {m : ℕ} {A : Frac K} (n : ℤ)
    (hA : FracCoprime m A) : FracCoprime m (A ^ n) := by
  intro 𝔭 h𝔭
  rw [Units.val_zpow_eq_zpow_val, FractionalIdeal.count_zpow, hA 𝔭 h𝔭, mul_zero]

/-- **The `𝔭`-adic exponent of the relative norm of a fractional ideal coprime to `(m)` vanishes
at every prime dividing `(m)`.** -/
lemma count_relNormUnit_eq_zero {K E : Type} [Field K] [NumberField K] [Field E]
    [NumberField E] [Algebra K E] [FiniteDimensional K E] {m : ℕ} {𝔄 : Frac E}
    (h : FracCoprime (K := E) m 𝔄) (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h𝔭 : (m : 𝓞 K) ∈ 𝔭.asIdeal) :
    FractionalIdeal.count K 𝔭
        ((NK.CFTLib.ARL.relNormUnit (K := K) (L := E) 𝔄 : Frac K) :
          FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  rw [show ((NK.CFTLib.ARL.relNormUnit (K := K) (L := E) 𝔄 : Frac K) :
      FractionalIdeal (𝓞 K)⁰ K) = NK.CFTLib.ARL.relNormFI (K := K) (L := E)
        (𝔄 : FractionalIdeal (𝓞 E)⁰ E) from rfl,
    NK.CFTLib.ARL.count_relNormFI, NK.CFTLib.ARL.relNormExp]
  refine Finset.sum_eq_zero fun 𝔮 h𝔮 => ?_
  have h𝔮lies : 𝔮.asIdeal.LiesOver 𝔭.asIdeal :=
    (NK.GlobalCFT.Place.mem_primesOverFinite (K := K) (L := E)).mp h𝔮
  have hm𝔮 : (m : 𝓞 E) ∈ 𝔮.asIdeal := by
    have h1 : (m : 𝓞 K) ∈ 𝔮.asIdeal.under (𝓞 K) := by
      rw [← h𝔮lies.over]; exact h𝔭
    have h2 := (Ideal.mem_under (𝓞 K) 𝔮.asIdeal).mp h1
    rwa [map_natCast] at h2
  rw [h 𝔮 hm𝔮, mul_zero]

/-- **A prime ideal is coprime to a natural number that does not lie in it.** -/
lemma fracCoprime_primeUnit {K : Type} [Field K] [NumberField K] {m : ℕ}
    {𝔮 : IsDedekindDomain.HeightOneSpectrum (𝓞 K)} (h : (m : 𝓞 K) ∉ 𝔮.asIdeal) :
    FracCoprime m (NK.CFTLib.ARL.primeUnit 𝔮) := by
  classical
  intro 𝔭 h𝔭
  rw [NK.CFTLib.ARL.primeUnit_val, FractionalIdeal.count_maximal]
  rw [if_neg]
  intro hEq
  exact h (hEq ▸ h𝔭)

/-- **A natural number lying in a prime ideal of a number field has a prime divisor dividing the
norm of the ideal.** -/
lemma exists_prime_dvd_absNorm_of_mem {K : Type} [Field K] [NumberField K]
    (𝔭 : NK.Chebotarev.PrimeIdeal K) {M : ℕ} (hM : (M : 𝓞 K) ∈ 𝔭.asIdeal) :
    ∃ p : ℕ, p.Prime ∧ p ∣ M ∧ p ∣ Ideal.absNorm 𝔭.asIdeal := by
  classical
  refine ⟨Ideal.absNorm (𝔭.asIdeal.under ℤ), Nat.absNorm_under_prime 𝔭.asIdeal, ?_, ?_⟩
  · have h1 : (M : ℤ) ∈ Ideal.span {((Ideal.absNorm (𝔭.asIdeal.under ℤ) : ℕ) : ℤ)} := by
      rw [Int.ideal_span_absNorm_eq_self]
      exact (Ideal.mem_under ℤ 𝔭.asIdeal).mpr (by simpa using hM)
    exact Int.natCast_dvd_natCast.mp (Ideal.mem_span_singleton.mp h1)
  · exact Int.absNorm_under_dvd_absNorm 𝔭.asIdeal

/-- **`IsUnramified` and `ramificationIdxIn = 1` agree** for a finite Galois extension. -/
theorem isUnramified_iff_ramificationIdxIn_eq_one {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : NK.Chebotarev.PrimeIdeal K) :
    NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) p ↔
      p.asIdeal.ramificationIdxIn (𝓞 L) = 1 := by
  classical
  letI hMSA : MulSemiringAction (Gal(L/K)) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction (𝓞 K) K L (𝓞 L)
  haveI hGG : IsGaloisGroup (Gal(L/K)) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (Gal(L/K)) (𝓞 K) (𝓞 L) K L
  constructor
  · intro hunr
    obtain ⟨Q, hQ⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) p
    haveI : Q.asIdeal.IsPrime := Q.isPrime
    haveI : Q.asIdeal.LiesOver p.asIdeal := hQ
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal Q.asIdeal (Gal(L/K))]
    exact hunr Q hQ
  · intro h Q hQ
    haveI : Q.asIdeal.IsPrime := Q.isPrime
    haveI : Q.asIdeal.LiesOver p.asIdeal := hQ
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx p.asIdeal Q.asIdeal (Gal(L/K))]
    exact h

/-- **Descent of unramifiedness to an intermediate field.** -/
theorem isUnramified_intermediateField {K Ω : Type} [Field K] [NumberField K] [Field Ω]
    [NumberField Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    (M : IntermediateField K Ω) [FiniteDimensional K M]
    {p : NK.Chebotarev.PrimeIdeal K}
    (h : Ideal.ramificationIdxIn p.asIdeal (𝓞 Ω) = 1) :
    NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥M) p := by
  intro P hP
  haveI : P.asIdeal.IsPrime := P.isPrime
  haveI : P.asIdeal.LiesOver p.asIdeal := hP
  obtain ⟨Q, hQ⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
    (K := ↥M) (L := Ω) P
  haveI : Q.asIdeal.IsPrime := Q.isPrime
  haveI : Q.asIdeal.LiesOver P.asIdeal := hQ
  haveI hQp : Q.asIdeal.LiesOver p.asIdeal :=
    Ideal.LiesOver.trans (𝔓 := Q.asIdeal) (P := P.asIdeal) (p := p.asIdeal)
  have hunr : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := Ω) p :=
    (isUnramified_iff_ramificationIdxIn_eq_one (K := K) (L := Ω) p).mpr h
  have hQunr : Q.asIdeal.ramificationIdx (𝓞 K) = 1 := hunr Q hQp
  have hmul : Q.asIdeal.ramificationIdx (𝓞 K)
      = P.asIdeal.ramificationIdx (𝓞 K) * Q.asIdeal.ramificationIdx (𝓞 ↥M) :=
    Ideal.ramificationIdx_tower (q := P.asIdeal) (r := Q.asIdeal)
  rw [hQunr] at hmul
  exact Nat.eq_one_of_mul_eq_one_right hmul.symm

/-- **`count` determines a nonzero fractional ideal.** -/
theorem fractionalIdeal_eq_of_count_eq {R : Type*} [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      FractionalIdeal.count K v I = FractionalIdeal.count K v J) : I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v => by rw [h v]

/-- The exponent-vector factorisation of a unit of the group of fractional ideals. -/
theorem frac_eq_finsupp_prod {K : Type*} [Field K] [NumberField K] (A : Frac K) :
    A = (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)).prod
        (fun 𝔭 e => (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) ^ e) := by
  have hcoe : (((NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)).prod
        (fun 𝔭 e => (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) ^ e) : Frac K) :
          FractionalIdeal (𝓞 K)⁰ K)
      = (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)).prod
          (fun 𝔭 e => (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ e) := by
    rw [Finsupp.prod, Finsupp.prod, Units.coe_prod]
    refine Finset.prod_congr rfl fun 𝔭 _ => ?_
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  have hne : (((NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)).prod
        (fun 𝔭 e => (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) ^ e) : Frac K) :
          FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [hcoe, Finsupp.prod]
    refine Finset.prod_ne_zero_iff.mpr fun 𝔭 _ => zpow_ne_zero _ ?_
    exact FractionalIdeal.coeIdeal_ne_zero.mpr 𝔭.ne_bot
  refine Units.ext (fractionalIdeal_eq_of_count_eq K (Units.ne_zero A) hne ?_)
  intro v
  rw [hcoe, FractionalIdeal.count_finsuppProd, NK.CFTLib.Arl.exps_apply]

/-- A product of integer powers of a fixed element of a commutative group is the power by the
sum of the exponents. -/
theorem finset_prod_zpow {ι G : Type*} [CommGroup G] (s : Finset ι) (g : G) (f : ι → ℤ) :
    ∏ i ∈ s, g ^ (f i) = g ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, zpow_zero]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

/-- The Artin symbol is multiplicative over natural powers. -/
theorem artinSym_pow {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcomm : ∀ a b : Gal(L/K), a * b = b * a) (A : FractionalIdeal (𝓞 K)⁰ K) (hA : A ≠ 0)
    (n : ℕ) :
    NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm (A ^ n)
      = (NK.CFTLib.Arl.artinSym (K := K) (L := L) hcomm A) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact NK.CFTLib.Arl.artinSym_one hcomm
  | succ n ih =>
      rw [pow_succ, NK.CFTLib.Arl.artinSym_mul hcomm (pow_ne_zero n hA) hA, ih, pow_succ]

/-- **The chosen Frobenius element restricts to the chosen Frobenius element of an intermediate
field**, at a prime whose ramification index in the big extension is one. -/
theorem frobAtPrime_restrictNormalHom {K Ω : Type} [Field K] [NumberField K] [Field Ω]
    [NumberField Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    [IsMulCommutative (Gal(Ω/K))]
    (M : IntermediateField K Ω) [FiniteDimensional K M] [NumberField ↥M] [Normal K M]
    [IsGalois K ↥M] [IsMulCommutative (Gal(↥M/K))]
    (p : NK.Chebotarev.PrimeIdeal K) (h : Ideal.ramificationIdxIn p.asIdeal (𝓞 Ω) = 1) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M
        (NK.Chebotarev.frobAtPrime (K := K) (L := Ω) p)
      = NK.Chebotarev.frobAtPrime (K := K) (L := ↥M) p := by
  classical
  have hcommL : ∀ a b : Gal(Ω/K), a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  have hcommM : ∀ a b : Gal(↥M/K), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  have hL : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := Ω) p :=
    (isUnramified_iff_ramificationIdxIn_eq_one p).mpr h
  have hM : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥M) p :=
    isUnramified_intermediateField (K := K) (Ω := Ω) M h
  obtain ⟨σ, hσ⟩ := NK.Chebotarev.exists_isFrobAtPrime (K := K) (L := Ω) p
  have h1 : NK.Chebotarev.frobAtPrime (K := K) (L := Ω) p = σ :=
    (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcommL p hL σ).mp hσ
  have h2 : NK.Chebotarev.frobAtPrime (K := K) (L := ↥M) p
      = AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M σ :=
    (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcommM p hM _).mp
      (NK.CFTLib.exists_isFrobAtPrime_restrict M hσ)
  rw [h1, h2]

/-- **The Artin symbol is compatible with restriction to an intermediate field**, for fractional
ideals whose prime factors are unramified in the big extension. -/
theorem artinSymFrac_restrictNormalHom {K Ω : Type} [Field K] [NumberField K] [Field Ω]
    [NumberField Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    [IsMulCommutative (Gal(Ω/K))]
    (M : IntermediateField K Ω) [FiniteDimensional K M] [NumberField ↥M] [Normal K M]
    [IsGalois K ↥M] [IsMulCommutative (Gal(↥M/K))]
    (hcomm : ∀ a b : Gal(Ω/K), a * b = b * a)
    (hcommM : ∀ a b : Gal(↥M/K), a * b = b * a)
    (𝔄 : Frac K)
    (hunr : ∀ p : NK.Chebotarev.PrimeIdeal K,
      NK.CFTLib.Arl.exps (𝔄 : FractionalIdeal (𝓞 K)⁰ K) p ≠ 0 →
      Ideal.ramificationIdxIn p.asIdeal (𝓞 Ω) = 1) :
    AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M
        (NK.CFTLib.Arl.artinSym (K := K) (L := Ω) hcomm (𝔄 : FractionalIdeal (𝓞 K)⁰ K))
      = NK.CFTLib.Arl.artinSym (K := K) (L := ↥M) hcommM
          (𝔄 : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  let Φ : Frac K →* Gal(Ω/K) := NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom hcomm
  let ΦM : Frac K →* Gal(↥M/K) := NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom hcommM
  set S : Finset (NK.Chebotarev.PrimeIdeal K) :=
    (NK.CFTLib.Arl.exps (𝔄 : FractionalIdeal (𝓞 K)⁰ K)).support with hS
  have hfac : 𝔄 = ∏ p ∈ S, (NK.CFTLib.ARL.primeUnit p) ^
      (NK.CFTLib.Arl.exps (𝔄 : FractionalIdeal (𝓞 K)⁰ K)) p := by
    rw [hS]; exact frac_eq_finsupp_prod 𝔄
  have hprime : ∀ p ∈ S,
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M) (Φ (NK.CFTLib.ARL.primeUnit p))
        = ΦM (NK.CFTLib.ARL.primeUnit p) := by
    intro p hp
    have hmem : NK.CFTLib.Arl.exps (𝔄 : FractionalIdeal (𝓞 K)⁰ K) p ≠ 0 :=
      Finsupp.mem_support_iff.mp hp
    simp only [Φ, ΦM, NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
      NK.CFTLib.ARL.primeUnit_val]
    rw [NK.CFTLib.Arl.artinSym_prime (K := K) (L := Ω) hcomm p,
      NK.CFTLib.Arl.artinSym_prime (K := K) (L := ↥M) hcommM p]
    exact frobAtPrime_restrictNormalHom (K := K) (Ω := Ω) M p (hunr p hmem)
  have hmain : (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M) (Φ 𝔄) = ΦM 𝔄 := by
    conv_lhs => rw [hfac]
    conv_rhs => rw [hfac]
    rw [map_prod Φ, map_prod ΦM, map_prod]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [map_zpow, map_zpow, map_zpow, hprime p hp]
  simpa only [Φ, ΦM, NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply] using hmain


/-! ## The transfer -/

set_option maxHeartbeats 4000000 in
theorem transferAux (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
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
  intro A hcop hsym
  classical
  have hcomm : ∀ a b : Gal(L/K), a * b = b * a := fun a b => IsMulCommutative.is_comm.comm a b
  set PN : Subgroup (Frac K) :=
    NK.CFTLib.ArtinReciprocityIdeal.principalRay K m ⊔
      NK.CFTLib.ArtinReciprocityIdeal.normRay K L m with hPNdef
  -- the trivial case
  by_cases hA1 : A = 1
  · rw [hA1]; exact Subgroup.one_mem _
  -- the support of `A`
  set s : Finset (NK.Chebotarev.PrimeIdeal K) :=
    (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)).support with hsdef
  have hsmem : ∀ 𝔭 ∈ s, (m : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro 𝔭 h𝔭 hmem
    have h0 : NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K) 𝔭 = 0 := by
      rw [NK.CFTLib.Arl.exps_apply]
      exact hcop 𝔭 hmem
    exact (Finsupp.mem_support_iff.mp h𝔭) h0
  -- the auxiliary-field hypothesis
  obtain ⟨M, hMne, hMcop, -, hMN, hdisjLK, E, hdisjEL, hE𝔭⟩ := haux s hsmem ∅ (by simp)
  haveI hMneI : NeZero M := hMne
  -- a generator of the cyclic group `Gal(L/K)`
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  -- the exponents of the Artin symbols of the primes of `s`
  have hexp : ∀ 𝔭 ∈ s, ∃ t : ℤ, NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭 = σ ^ t :=
    fun 𝔭 _ => by
      obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp (hσ _)
      exact ⟨t, ht.symm⟩
  let sEx : NK.Chebotarev.PrimeIdeal K → ℤ := fun 𝔭 =>
    if h : 𝔭 ∈ s then Classical.choose (hexp 𝔭 h) else 0
  have hsEx : ∀ 𝔭 ∈ s, NK.Chebotarev.frobAtPrime (K := K) (L := L) 𝔭 = σ ^ (sEx 𝔭) := by
    intro 𝔭 h𝔭
    simp only [sEx, dif_pos h𝔭]
    exact Classical.choose_spec (hexp 𝔭 h𝔭)
  -- the Artin symbol of `A` is `σ ^ (Σ e 𝔭 · s 𝔭)`
  set N : ℤ := ∑ 𝔭 ∈ s, (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭 * sEx 𝔭
    with hNdef
  have hσN : σ ^ N = 1 := by
    have hΨ : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom hcomm A = 1 := by
      rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply]
      exact hsym
    have hfac : A = ∏ 𝔭 ∈ s,
        (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K)
          ^ (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭 := by
      rw [hsdef]
      exact frac_eq_finsupp_prod A
    have hprimeVal : ∀ 𝔭 ∈ s,
        NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom hcomm
            (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) = σ ^ (sEx 𝔭) := by
      intro 𝔭 h𝔭
      rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
        show ((idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) : FractionalIdeal (𝓞 K)⁰ K)
          = (𝔭.asIdeal : FractionalIdeal (𝓞 K)⁰ K) from rfl,
        NK.CFTLib.Arl.artinSym_prime (K := K) (L := L) hcomm 𝔭]
      exact hsEx 𝔭 h𝔭
    have hkey : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom hcomm A = σ ^ N := by
      rw [hfac, map_prod, Finset.prod_congr rfl (fun 𝔭 h𝔭 => by
        rw [map_zpow, hprimeVal 𝔭 h𝔭, ← zpow_mul, mul_comm])]
      rw [finset_prod_zpow s σ]
    rw [← hkey]
    exact hΨ
  -- the exponent is a multiple of `[L : K]`
  have hn : Nat.card (Gal(L/K)) = Module.finrank K L := IsGalois.card_aut_eq_finrank K L
  have horder : orderOf σ = Module.finrank K L := by
    rw [← hn]
    exact orderOf_eq_card_of_forall_mem_zpowers hσ
  have hdvd : (Module.finrank K L : ℤ) ∣ N := by
    rw [← horder]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hσN
  -- ### the auxiliary fields `E𝔭`
  have hE' : ∀ 𝔭 : {𝔭 : NK.Chebotarev.PrimeIdeal K // 𝔭 ∈ s},
      ∃ E𝔭 : IntermediateField K (CyclotomicField M L),
        E𝔭 ≤ E ∧
        (E𝔭.restrictScalars ℚ) ⊔ (IntermediateField.adjoin ℚ
          ({IsCyclotomicExtension.zeta M L (CyclotomicField M L)} :
            Set (CyclotomicField M L))) = ⊤ ∧
        NK.Chebotarev.IsFrobAtPrime (K := K) (L := ↥E𝔭) 𝔭.1 1 :=
    fun 𝔭 => hE𝔭 𝔭.1 𝔭.2
  choose Ef hEfle hEfjoin hEfsplit using hE'
  -- the image of `L` in `Ω = L(ζ_M)`
  set LΩ : IntermediateField K (CyclotomicField M L) :=
    (⊥ : IntermediateField L (CyclotomicField M L)).restrictScalars K with hLΩdef
  -- `s` is nonempty because `A ≠ 1`
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    apply hA1
    have h0 : NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
      rw [Finsupp.ext_iff]
      intro 𝔭
      rw [Finsupp.zero_apply]
      by_contra hne
      have hmem : 𝔭 ∈ s := by rw [hsdef]; exact Finsupp.mem_support_iff.mpr hne
      rw [h] at hmem
      exact Finset.notMem_empty 𝔭 hmem
    rw [frac_eq_finsupp_prod A, h0]
    exact Finsupp.prod_zero_index
  -- the cyclotomic structure of `Ω` over the auxiliary fields
  have hcyc : ∀ 𝔭 : {𝔭 : NK.Chebotarev.PrimeIdeal K // 𝔭 ∈ s},
      IsCyclotomicExtension {M} ↥(Ef 𝔭) (CyclotomicField M L) :=
    fun 𝔭 => NK.CFTLib.ARLAlt.isCyclotomicExtension_of_sup_adjoin_zeta
      (K := K) (L := L) M (Ef 𝔭) (hEfjoin 𝔭)
  have hcycE : IsCyclotomicExtension {M} ↥E (CyclotomicField M L) := by
    obtain ⟨𝔭₀, h𝔭₀⟩ := hsne
    refine NK.CFTLib.ARLAlt.isCyclotomicExtension_of_sup_adjoin_zeta (K := K) (L := L) M E ?_
    rw [eq_top_iff]
    refine le_trans (le_of_eq (hEfjoin ⟨𝔭₀, h𝔭₀⟩).symm) ?_
    exact sup_le_sup_right (fun x hx => hEfle ⟨𝔭₀, h𝔭₀⟩ hx) _
  -- primes of `↥E𝔭` (resp. `↥E`) not dividing `(M)` are unramified in `Ω`
  have hunr_cyc : ∀ 𝔭 : {𝔭 : NK.Chebotarev.PrimeIdeal K // 𝔭 ∈ s},
      ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥(Ef 𝔭),
        (M : 𝓞 ↥(Ef 𝔭)) ∉ 𝔮.asIdeal →
        NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥(Ef 𝔭))
          (L := CyclotomicField M L) 𝔮 :=
    fun 𝔭 𝔮 h𝔮 => by
      haveI := hcyc 𝔭
      exact NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (k := ↥(Ef 𝔭))
        (Ω := CyclotomicField M L) M 𝔮 h𝔮
  have hunr_cycE : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥E,
      (M : 𝓞 ↥E) ∉ 𝔮.asIdeal →
      NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E) (L := CyclotomicField M L) 𝔮 :=
    fun 𝔮 h𝔮 => by
      haveI := hcycE
      exact NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (k := ↥E)
        (Ω := CyclotomicField M L) M 𝔮 h𝔮
  -- ### Galois-theoretic setup
  have hdisjEL' : E ⊓ LΩ = ⊥ := disjoint_iff.mp hdisjEL
  haveI hGalΩ0 : IsGalois K (CyclotomicField M L) :=
    NK.CFTLib.ARL.isGalois_cyclotomicField_over_base (K := K) (L := L) M
  have hcommΩ : ∀ a b : Gal(CyclotomicField M L / K), a * b = b * a :=
    NK.CFTLib.ARL.TFH.mul_comm_cyclotomicField hcomm M
  have hGalF : ∀ F : IntermediateField K (CyclotomicField M L), IsGalois K ↥F :=
    fun F => NK.CFTLib.ARL.TFH.isGalois_intermediateField_cyclotomicField_aux hcomm M F
  haveI hGalE : IsGalois K ↥E := hGalF E
  haveI hGalLΩ : IsGalois K ↥LΩ := hGalF LΩ
  haveI hGalΩE : IsGalois ↥E (CyclotomicField M L) :=
    IsGalois.tower_top_of_isGalois K ↥E _
  haveI hfinΩE : FiniteDimensional ↥E (CyclotomicField M L) :=
    IsCyclotomicExtension.finiteDimensional {M} ↥E (CyclotomicField M L)
  haveI habE : IsAbelianGalois ↥E (CyclotomicField M L) :=
    IsCyclotomicExtension.isAbelianGalois {M} ↥E (CyclotomicField M L)
  haveI hcommE' : IsMulCommutative (Gal((CyclotomicField M L)/↥E)) := habE.toIsMulCommutative
  have hcommE : ∀ a b : Gal(CyclotomicField M L / ↥E), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  haveI hcommLΩI : IsMulCommutative (Gal(↥LΩ/K)) := by
    rw [hLΩdef]
    exact NK.CFTLib.ARL.TFH.isMulCommutative_LImage (K := K) (L := L) M
  have hcommLΩ : ∀ a b : Gal(↥LΩ/K), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  -- ### the isomorphism `↥LΩ ≃ₐ[K] L` and the conjugate generator
  let eL : ↥LΩ ≃ₐ[K] L := hLΩdef ▸ NK.CFTLib.ARLAlt.LImageEquiv (K := K) (L := L) M
  let σΩ : Gal(↥LΩ/K) := NK.CFTLib.ARL.TFH.conjHom eL.symm σ
  -- ### the modulus and the ramification hypotheses
  set c : ℕ := m * M with hcdef
  have hcpos : 0 < c := by rw [hcdef]; exact Nat.mul_pos hm (NeZero.pos M)
  have hramΩE : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥E,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥E)
        (L := CyclotomicField M L) 𝔮 → (c : 𝓞 ↥E) ∈ 𝔮.asIdeal := by
    intro 𝔮 h
    have hM : (M : 𝓞 ↥E) ∈ 𝔮.asIdeal := by
      by_contra hM
      exact h (hunr_cycE 𝔮 hM)
    rw [hcdef, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ hM
  have hramLΩ : ∀ p : NK.Chebotarev.PrimeIdeal K,
      ¬ NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥LΩ) p →
      (c : 𝓞 K) ∈ p.asIdeal := by
    intro p hp
    by_contra hc
    rw [hLΩdef] at hp
    have hm_p : (m : 𝓞 K) ∉ p.asIdeal := fun hmem =>
      hc (by rw [hcdef, Nat.cast_mul]; exact Ideal.mul_mem_right (M : 𝓞 K) p.asIdeal hmem)
    have hM_p : (M : 𝓞 K) ∉ p.asIdeal := fun hmem =>
      hc (by rw [hcdef, Nat.cast_mul]; exact Ideal.mul_mem_left p.asIdeal (m : 𝓞 K) hmem)
    exact hp (NK.CFTLib.ARL.TFH.isUnramified_LImage (K := K) (L := L) M m hram p hm_p hM_p)
  -- ### a lift of `σΩ` to `Gal(Ω/↥E)`
  obtain ⟨σ', hσ'⟩ := NK.CFTLib.ARL.TFH.restrictNormalHom_comp_restrictScalars_surjective
    (K := K) (Ω := CyclotomicField M L) E LΩ hdisjEL' σΩ
  -- ### the auxiliary ideal `𝔅` and the common norm `𝔟`
  obtain ⟨𝔅, h𝔅ψ⟩ := NK.CFTLib.ArtinReciprocityIdeal.artinSymSurjectiveOnCoprime
    (K := ↥E) (L := CyclotomicField M L) c hcpos hramΩE σ'
  have h𝔅cop : NK.CFTLib.ArtinReciprocityIdeal.FracCoprime (K := ↥E) c
      (𝔅 : Frac ↥E) :=
    (NK.CFTLib.ArtinReciprocityIdeal.mem_idealCoprimeGroup_iff (K := ↥E) c
      (𝔅 : Frac ↥E)).mp 𝔅.2
  set 𝔟 : Frac K := NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥E) (𝔅 : Frac ↥E)
    with h𝔟def
  have hcompat := NK.CFTLib.ArtinReciprocityIdeal.artinSym_restrict_relNorm_of_normal
    (K := K) (M := CyclotomicField M L) E LΩ hcommE hcommLΩ c hramΩE hramLΩ
    (𝔅 : Frac ↥E) h𝔅cop
  have h𝔟ψ : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom hcommLΩ 𝔟 = σΩ := by
    rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply, h𝔟def, ← hcompat, h𝔅ψ]
    simpa only [NK.CFTLib.Arl.restrictScalarsHom_apply, MonoidHom.comp_apply] using hσ'
  -- ### the primes of `s` are coprime to `M`
  have hpM : ∀ 𝔭 ∈ s, (M : 𝓞 K) ∉ 𝔭.asIdeal := by
    intro 𝔭 h𝔭 hmem
    obtain ⟨p, hp, hpM', hpdvd⟩ := exists_prime_dvd_absNorm_of_mem 𝔭 hmem
    exact hMN p hp hpM' 𝔭 h𝔭 hpdvd
  -- ### `𝔭` is unramified in `↥LΩ`
  have hfrobLΩ : ∀ 𝔭 : {𝔭 : NK.Chebotarev.PrimeIdeal K // 𝔭 ∈ s},
      NK.Chebotarev.frobAtPrime (K := K) (L := ↥LΩ) 𝔭.1 = σΩ ^ (sEx 𝔭.1) := by
    intro 𝔭
    have h𝔭unr : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := L) 𝔭.1 := by
      by_contra h
      exact hsmem 𝔭.1 𝔭.2 (hram 𝔭.1 h)
    have h𝔭unrΩ : NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := K) (L := ↥LΩ) 𝔭.1 :=
      hLΩdef ▸ NK.CFTLib.ARL.TFH.isUnramified_LImage (K := K) (L := L) M m hram 𝔭.1
        (hsmem 𝔭.1 𝔭.2) (hpM 𝔭.1 𝔭.2)
    refine (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcommLΩ 𝔭.1 h𝔭unrΩ _).mp ?_
    have h1 : NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) 𝔭.1 (σ ^ sEx 𝔭.1) := by
      rw [← hsEx 𝔭.1 𝔭.2]
      exact NK.Chebotarev.isFrobAtPrime_frobAtPrime hcomm 𝔭.1 h𝔭unr
    have h2 := (NK.Chebotarev.IsFrobAtPrimeAlgEquivSameBase (K := K) eL.symm
      (σ ^ sEx 𝔭.1) 𝔭.1).mp h1
    rwa [show (AlgEquiv.symm eL).symm.trans ((σ ^ sEx 𝔭.1).trans eL.symm)
        = σΩ ^ sEx 𝔭.1 from
      map_zpow (NK.CFTLib.ARL.TFH.conjHom eL.symm) σ (sEx 𝔭.1)] at h2
  -- ### the `[L : K]`-th power of `𝔟` lies in the norm ray
  have h𝔟cop : FracCoprime m 𝔟 := by
    intro 𝔮 h𝔮
    rw [h𝔟def]
    refine count_relNormUnit_eq_zero (K := K) (E := ↥E) h𝔅cop 𝔮 ?_
    rw [hcdef, Nat.cast_mul]
    exact Ideal.mul_mem_right (M : 𝓞 K) 𝔮.asIdeal h𝔮
  have h𝔟pow : 𝔟 ^ Module.finrank K L ∈
      NK.CFTLib.ArtinReciprocityIdeal.normRay K L m :=
    NK.Existence.ArtinLemma.pow_finrank_mem_normRay m h𝔟cop
  -- ### the per-prime step
  have hper : ∀ 𝔭 : {𝔭 : NK.Chebotarev.PrimeIdeal K // 𝔭 ∈ s},
      (idealUnit 𝔭.1.asIdeal 𝔭.1.ne_bot : Frac K) ^
          (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭.1 *
        𝔟 ^ (-((NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭.1 * sEx 𝔭.1)) ∈ PN := by
    intro 𝔭
    haveI : IsMulCommutative (Gal(↥LΩ/K)) := hcommLΩI
    -- the tower `↥(Ef 𝔭) ⊆ ↥E`
    letI : Algebra ↥(Ef 𝔭) ↥E := NK.CFTLib.ARL.TFH.algOfLe (Ef 𝔭) E (hEfle 𝔭)
    haveI : IsScalarTower K ↥(Ef 𝔭) ↥E :=
      NK.CFTLib.ARL.TFH.isScalarTower_algOfLe (Ef 𝔭) E (hEfle 𝔭)
    haveI : FiniteDimensional ↥(Ef 𝔭) ↥E :=
      NK.CFTLib.ARL.TFH.finiteDimensional_algOfLe (Ef 𝔭) E (hEfle 𝔭)
    obtain ⟨𝔓, h𝔓lies, h𝔓frob⟩ := hEfsplit 𝔭
    haveI h𝔓over : 𝔓.asIdeal.LiesOver 𝔭.1.asIdeal := h𝔓lies
    have hrelNorm : Ideal.relNorm (𝓞 K) 𝔓.asIdeal = 𝔭.1.asIdeal :=
      NK.CFTLib.ARLAlt.relNorm_prime_eq_of_isFrobAt_one h𝔓lies h𝔓frob
    -- the auxiliary ideal `𝔠 = N_{E𝔭/E}𝔅` and `𝔘 = 𝔓^e·𝔠^{-e·s}`
    set 𝔠 : Frac ↥(Ef 𝔭) :=
      NK.CFTLib.ARL.relNormUnit (K := ↥(Ef 𝔭)) (L := ↥E) (𝔅 : Frac ↥E) with h𝔠def
    set 𝔘 : Frac ↥(Ef 𝔭) :=
      (NK.CFTLib.ARL.primeUnit 𝔓) ^
          (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭.1 *
        𝔠 ^ (-((NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭.1 * sEx 𝔭.1)) with h𝔘def
    -- the norm of `𝔘` down to `K`
    have hprime1 : NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef 𝔭))
        (NK.CFTLib.ARL.primeUnit 𝔓) = (idealUnit 𝔭.1.asIdeal 𝔭.1.ne_bot : Frac K) := by
      refine Units.ext ?_
      show NK.CFTLib.ARL.relNormFI (K := K) (L := ↥(Ef 𝔭))
          ((NK.CFTLib.ARL.primeUnit 𝔓 : Frac ↥(Ef 𝔭)) :
            FractionalIdeal (𝓞 ↥(Ef 𝔭))⁰ ↥(Ef 𝔭))
        = ((𝔭.1.asIdeal : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      rw [NK.CFTLib.ARL.primeUnit_val, NK.CFTLib.ARL.relNormFI_prime, hrelNorm]
    have h𝔘norm : NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef 𝔭)) 𝔘 =
        (idealUnit 𝔭.1.asIdeal 𝔭.1.ne_bot : Frac K) ^
            (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭.1 *
          𝔟 ^ (-((NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭.1 * sEx 𝔭.1)) := by
      rw [h𝔘def, map_mul, map_zpow, map_zpow, hprime1, h𝔠def]
      rw [NK.CFTLib.ARL.relNormUnit_trans (K := K) (E := ↥(Ef 𝔭)) (M := ↥E)
        (𝔅 : Frac ↥E), h𝔟def]
    -- the small facts
    have hm𝔭 : (m : 𝓞 K) ∉ 𝔭.1.asIdeal := hsmem 𝔭.1 𝔭.2
    have hpM𝔭 : (M : 𝓞 K) ∉ 𝔭.1.asIdeal := hpM 𝔭.1 𝔭.2
    have hM𝔓 : (M : 𝓞 ↥(Ef 𝔭)) ∉ 𝔓.asIdeal := by
      intro hmem
      have h1 : (M : ℤ) ∈ 𝔓.asIdeal.under ℤ :=
        (Ideal.mem_under ℤ 𝔓.asIdeal).mpr (by simpa using hmem)
      have hunder : 𝔓.asIdeal.under ℤ = 𝔭.1.asIdeal.under ℤ := by
        rw [← Ideal.under_under (A := ℤ) (B := 𝓞 K) 𝔓.asIdeal, ← h𝔓lies.over]
      have h2 : (M : ℤ) ∈ Ideal.span
          {((Ideal.absNorm (𝔭.1.asIdeal.under ℤ) : ℕ) : ℤ)} := by
        rw [Int.ideal_span_absNorm_eq_self, ← hunder]
        exact h1
      exact hMN _ (Nat.absNorm_under_prime 𝔭.1.asIdeal)
        (Int.natCast_dvd_natCast.mp (Ideal.mem_span_singleton.mp h2)) 𝔭.1 𝔭.2
        (Int.absNorm_under_dvd_absNorm 𝔭.1.asIdeal)
    have hm𝔓 : (m : 𝓞 ↥(Ef 𝔭)) ∉ 𝔓.asIdeal := by
      intro hmem
      refine hm𝔭 ?_
      rw [Ideal.mem_of_liesOver 𝔓.asIdeal 𝔭.1.asIdeal (m : 𝓞 K), map_natCast]
      exact hmem
    have hc𝔓 : (c : 𝓞 ↥(Ef 𝔭)) ∉ 𝔓.asIdeal := by
      intro hmem
      rw [hcdef, Nat.cast_mul] at hmem
      rcases 𝔓.isPrime.mem_or_mem hmem with h' | h'
      · exact hm𝔓 h'
      · exact hM𝔓 h'
    -- `𝔘` is coprime to `(c)`
    have h𝔠cop : FracCoprime (K := ↥(Ef 𝔭)) c 𝔠 := by
      intro 𝔮 h𝔮
      exact count_relNormUnit_eq_zero (K := ↥(Ef 𝔭)) (E := ↥E) h𝔅cop 𝔮 h𝔮
    have h𝔓cop : FracCoprime (K := ↥(Ef 𝔭)) c (NK.CFTLib.ARL.primeUnit 𝔓) :=
      fracCoprime_primeUnit hc𝔓
    have h𝔘cop : FracCoprime (K := ↥(Ef 𝔭)) c 𝔘 := by
      rw [h𝔘def]
      exact FracCoprime_mul (FracCoprime_zpow _ h𝔓cop) (FracCoprime_zpow _ h𝔠cop)
    -- the cyclotomic structure and commutativity at `E𝔭`
    haveI hcommEpI : IsMulCommutative (Gal((CyclotomicField M L)/↥(Ef 𝔭))) := by
      haveI hab := IsCyclotomicExtension.isAbelianGalois {M} ↥(Ef 𝔭) (CyclotomicField M L)
      exact hab.toIsMulCommutative
    have hcommEp : ∀ a b : Gal(CyclotomicField M L / ↥(Ef 𝔭)), a * b = b * a :=
      fun a b => IsMulCommutative.is_comm.comm a b
    haveI hGalΩEp : IsGalois ↥(Ef 𝔭) (CyclotomicField M L) :=
      IsGalois.tower_top_of_isGalois K ↥(Ef 𝔭) _
    haveI hfinΩEp : FiniteDimensional ↥(Ef 𝔭) (CyclotomicField M L) :=
      IsCyclotomicExtension.finiteDimensional {M} ↥(Ef 𝔭) (CyclotomicField M L)
    have hramΩEp : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥(Ef 𝔭),
        ¬NK.CFTLib.ArtinReciprocityIdeal.IsUnramified (K := ↥(Ef 𝔭))
          (L := CyclotomicField M L) 𝔮 → (c : 𝓞 ↥(Ef 𝔭)) ∈ 𝔮.asIdeal := by
      intro 𝔮 h
      have hMq : (M : 𝓞 ↥(Ef 𝔭)) ∈ 𝔮.asIdeal := by
        by_contra hMq
        exact h (hunr_cyc 𝔭 𝔮 hMq)
      rw [hcdef, Nat.cast_mul]
      exact Ideal.mul_mem_left _ _ hMq
    -- the restriction of `ψ_{Ω/E𝔭}(𝔘)` to `LΩ` is trivial
    have hcompatp : AlgEquiv.restrictNormalHom (F := K)
        (K₁ := CyclotomicField M L) LΩ
        ((NK.CFTLib.Arl.artinSym (K := ↥(Ef 𝔭)) (L := CyclotomicField M L) hcommEp
            𝔘).restrictScalars K)
        = NK.CFTLib.Arl.artinSym (K := K) (L := ↥LΩ) hcommLΩ
            (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef 𝔭)) 𝔘) :=
      NK.CFTLib.ArtinReciprocityIdeal.artinSym_restrict_relNorm_of_normal
        (K := K) (M := CyclotomicField M L) (Ef 𝔭) LΩ hcommEp hcommLΩ c hramΩEp hramLΩ
        𝔘 h𝔘cop
    have hfrobLΩ' : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom hcommLΩ
        (idealUnit 𝔭.1.asIdeal 𝔭.1.ne_bot : Frac K) = σΩ ^ (sEx 𝔭.1) := by
      rw [NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply,
        show ((idealUnit 𝔭.1.asIdeal 𝔭.1.ne_bot : Frac K) : FractionalIdeal (𝓞 K)⁰ K)
          = (𝔭.1.asIdeal : FractionalIdeal (𝓞 K)⁰ K) from rfl,
        NK.CFTLib.Arl.artinSym_prime (K := K) (L := ↥LΩ) hcommLΩ 𝔭.1]
      exact hfrobLΩ 𝔭
    have hN𝔘 : NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom hcommLΩ
        (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef 𝔭)) 𝔘) = 1 := by
      rw [h𝔘norm, map_mul, map_zpow, map_zpow, hfrobLΩ', h𝔟ψ, ← zpow_mul,
        mul_comm (sEx 𝔭.1) ((NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭.1),
        zpow_neg]
      exact mul_inv_cancel _
    have hN𝔘' : NK.CFTLib.Arl.artinSym (K := K) (L := ↥LΩ) hcommLΩ
        (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef 𝔭)) 𝔘) = 1 := by
      rw [← NK.CFTLib.ArtinReciprocityIdeal.artinSymFracHom_apply]
      exact hN𝔘
    have hker : AlgEquiv.restrictNormalHom (F := K) (K₁ := CyclotomicField M L) LΩ
        ((NK.CFTLib.Arl.artinSym (K := ↥(Ef 𝔭)) (L := CyclotomicField M L) hcommEp
            𝔘).restrictScalars K) = 1 := by
      rw [hcompatp, hN𝔘']
    -- `ψ_{Ω/E𝔭}(𝔘)` fixes `LΩ ⊔ E𝔭` pointwise
    have hfixEp : ∀ x ∈ (Ef 𝔭 : Set (CyclotomicField M L)),
        NK.CFTLib.Arl.artinSym (K := ↥(Ef 𝔭)) (L := CyclotomicField M L) hcommEp 𝔘 x = x := by
      intro x hx
      exact (NK.CFTLib.Arl.artinSym (K := ↥(Ef 𝔭)) (L := CyclotomicField M L) hcommEp
        𝔘).commutes (⟨x, hx⟩ : ↥(Ef 𝔭))
    have hfixLΩ : ∀ x ∈ (LΩ : Set (CyclotomicField M L)),
        NK.CFTLib.Arl.artinSym (K := ↥(Ef 𝔭)) (L := CyclotomicField M L) hcommEp 𝔘 x = x := by
      intro x hx
      have h2 := congrArg (fun f : ↥LΩ ≃ₐ[K] ↥LΩ => (f ⟨x, hx⟩ : ↥LΩ)) hker
      have h3 := congrArg (fun z : ↥LΩ => (z : CyclotomicField M L)) h2
      simp only [AlgEquiv.one_apply] at h3
      rw [AlgEquiv.restrictNormalHom_apply] at h3
      exact h3
    have hfixLE : ∀ x ∈ ((Ef 𝔭) ⊔ LΩ : IntermediateField K (CyclotomicField M L)),
        NK.CFTLib.Arl.artinSym (K := ↥(Ef 𝔭)) (L := CyclotomicField M L) hcommEp 𝔘 x = x := by
      intro x hx
      have hle : (Ef 𝔭) ⊔ LΩ ≤ IntermediateField.fixedField
          (Subgroup.zpowers ((NK.CFTLib.Arl.artinSym (K := ↥(Ef 𝔭))
            (L := CyclotomicField M L) hcommEp 𝔘).restrictScalars K)) := by
        refine sup_le ?_ ?_
        · rw [IntermediateField.le_iff_le, Subgroup.zpowers_le,
            IntermediateField.mem_fixingSubgroup_iff]
          intro y hy
          rw [AlgEquiv.restrictScalars_apply]
          exact hfixEp y hy
        · rw [IntermediateField.le_iff_le, Subgroup.zpowers_le,
            IntermediateField.mem_fixingSubgroup_iff]
          intro y hy
          rw [AlgEquiv.restrictScalars_apply]
          exact hfixLΩ y hy
      have h3 : ((NK.CFTLib.Arl.artinSym (K := ↥(Ef 𝔭)) (L := CyclotomicField M L)
          hcommEp 𝔘).restrictScalars K) x = x :=
        (IntermediateField.mem_fixedField_iff _ x).mp (hle hx) _ (Subgroup.mem_zpowers _)
      rwa [AlgEquiv.restrictScalars_apply] at h3
    -- the cell's field: Galois and commutative over `E𝔭`
    haveI hcommCellI : IsMulCommutative
        (Gal(↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left)/↥(Ef 𝔭))) :=
      NK.CFTLib.ARLAlt.isMulCommutative_ofLe_sup M (Ef 𝔭) (hEfjoin 𝔭)
    have hcommCell : ∀ a b : Gal(↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭)
        ((Ef 𝔭) ⊔ LΩ) le_sup_left)/↥(Ef 𝔭)), a * b = b * a :=
      fun a b => IsMulCommutative.is_comm.comm a b
    haveI hGalCell : IsGalois ↥(Ef 𝔭)
        ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left) :=
      NK.CFTLib.ARLAlt.isGalois_ofLe_sup (K := K) (L := L) M (Ef 𝔭)
    -- the Artin symbol of `𝔘` in the cell vanishes
    have h𝔘ψ : NK.CFTLib.Arl.artinSym (K := ↥(Ef 𝔭))
        (L := ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left))
        hcommCell 𝔘 = 1 := by
      have hR := artinSymFrac_restrictNormalHom (K := ↥(Ef 𝔭))
        (Ω := CyclotomicField M L)
        (M := NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left)
        hcommEp hcommCell 𝔘 (fun q hq => by
          have hMq : (M : 𝓞 ↥(Ef 𝔭)) ∉ q.asIdeal := by
            by_contra hMq
            exact hq (h𝔘cop q (by
              rw [hcdef, Nat.cast_mul]
              exact Ideal.mul_mem_left _ _ hMq))
          exact (isUnramified_iff_ramificationIdxIn_eq_one (K := ↥(Ef 𝔭))
            (L := CyclotomicField M L) q).mp (hunr_cyc 𝔭 q hMq))
      rw [← hR]
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      rw [AlgEquiv.restrictNormalHom_apply]
      exact hfixLE ↑x x.2
    -- the cyclotomic cell at `E𝔭`
    have hcell : 𝔘 ∈ NK.CFTLib.ArtinReciprocityIdeal.principalRay ↥(Ef 𝔭) c ⊔
        NK.CFTLib.ArtinReciprocityIdeal.normRay ↥(Ef 𝔭)
          ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left) c :=
      NK.CFTLib.ARLAlt.cellAtAuxField (K := K) (L := L) M (Ef 𝔭) (hEfjoin 𝔭) c hcpos
        ⟨m, by rw [hcdef, mul_comm]⟩ (fun q h => by
          have hMq : (M : 𝓞 ↥(Ef 𝔭)) ∈ q.asIdeal := by
            by_contra hMq
            exact h (NK.CFTLib.ARL.TFH.isUnramified_cellAtAux M (Ef 𝔭) (hEfjoin 𝔭) q hMq)
          rw [hcdef, Nat.cast_mul]
          exact Ideal.mul_mem_left _ _ hMq) 𝔘 h𝔘cop h𝔘ψ
    -- the norm of `𝔘` down to `K` lies in `P(m)·𝔑(m)`
    rw [← h𝔘norm]
    have hmem : (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef 𝔭)) 𝔘) ∈
        Subgroup.map (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef 𝔭)))
          (NK.CFTLib.ArtinReciprocityIdeal.principalRay ↥(Ef 𝔭) c ⊔
            NK.CFTLib.ArtinReciprocityIdeal.normRay ↥(Ef 𝔭)
              ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left) c) :=
      Subgroup.mem_map_of_mem _ hcell
    have hle : Subgroup.map (NK.CFTLib.ARL.relNormUnit (K := K) (L := ↥(Ef 𝔭)))
        (NK.CFTLib.ArtinReciprocityIdeal.principalRay ↥(Ef 𝔭) c ⊔
          NK.CFTLib.ArtinReciprocityIdeal.normRay ↥(Ef 𝔭)
            ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left) c) ≤ PN := by
      rw [Subgroup.map_sup, hPNdef]
      refine sup_le ?_ ?_
      · exact le_sup_of_le_left (NK.CFTLib.ARLAlt.principalRay_map_relNormUnit_le
          (K := K) (E := ↥(Ef 𝔭)) c m hm hcpos ⟨M, by rw [hcdef]⟩)
      refine le_sup_of_le_right (le_trans ?_ (NK.CFTLib.ARL.TFH.normRay_le_of_algEquiv eL.symm m))
      · letI : Algebra ↥LΩ ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭)
            ((Ef 𝔭) ⊔ LΩ) le_sup_left) :=
          NK.CFTLib.ARL.TFH.algOfLe LΩ ((Ef 𝔭) ⊔ LΩ) le_sup_right
        haveI : IsScalarTower K ↥LΩ
            ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left) :=
          NK.CFTLib.ARL.TFH.isScalarTower_algOfLe LΩ ((Ef 𝔭) ⊔ LΩ) le_sup_right
        haveI : FiniteDimensional ↥LΩ
            ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left) :=
          NK.CFTLib.ARL.TFH.finiteDimensional_algOfLe LΩ ((Ef 𝔭) ⊔ LΩ) le_sup_right
        exact NK.CFTLib.ARLAlt.normRay_map_relNormUnit_le (K := K) (L := ↥LΩ)
          (E := ↥(Ef 𝔭))
          (LE := ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left))
          c m hm ⟨M, by rw [hcdef]⟩
    exact hle hmem
  -- ### the product of the `X𝔭`
  have hprod : (∏ 𝔭 ∈ s, (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) ^
      (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭) * 𝔟 ^ (-N) ∈ PN := by
    rw [show (∏ 𝔭 ∈ s, (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) ^
          (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭) * 𝔟 ^ (-N)
        = ∏ 𝔭 ∈ s, ((idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) ^
            (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭 *
              𝔟 ^ (-((NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭 *
                sEx 𝔭))) from ?_]
    · exact Subgroup.prod_mem _ fun 𝔭 h𝔭 => hper ⟨𝔭, h𝔭⟩
    · rw [Finset.prod_mul_distrib, finset_prod_zpow, Finset.sum_neg_distrib, ← hNdef]
  -- ### `𝔟 ^ N ∈ 𝔑(m)`
  have h𝔟N : 𝔟 ^ N ∈ PN := by
    obtain ⟨k, hk⟩ := hdvd
    have h1 : 𝔟 ^ N = (𝔟 ^ Module.finrank K L) ^ k := by
      rw [hk, zpow_mul, zpow_natCast]
    rw [hPNdef, h1]
    exact Subgroup.zpow_mem _ (Subgroup.mem_sup_right h𝔟pow) k
  -- ### conclusion
  rw [hPNdef]
  rw [show A = ∏ 𝔭 ∈ s, (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) ^
      (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭 from by
    rw [hsdef]; exact frac_eq_finsupp_prod A]
  have h2 := Subgroup.mul_mem _ hprod h𝔟N
  have h3 : (∏ 𝔭 ∈ s, (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) ^
      (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭) * 𝔟 ^ (-N) * 𝔟 ^ N
      = ∏ 𝔭 ∈ s, (idealUnit 𝔭.asIdeal 𝔭.ne_bot : Frac K) ^
        (NK.CFTLib.Arl.exps (A : FractionalIdeal (𝓞 K)⁰ K)) 𝔭 := by
    rw [mul_assoc, zpow_neg, inv_mul_cancel, mul_one]
  rwa [h3] at h2


end NK.CFTLib.ARL.TFP

namespace NK.CFTLib.ARL

theorem transfer_of_auxField (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
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
          NK.CFTLib.ArtinReciprocityIdeal.normRay K L m :=
  NK.CFTLib.ARL.TFP.transferAux K L m hm haux hram

end NK.CFTLib.ARL
