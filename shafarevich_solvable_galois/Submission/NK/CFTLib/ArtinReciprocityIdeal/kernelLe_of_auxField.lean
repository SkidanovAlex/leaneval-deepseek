
import Mathlib
import Submission.NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension
import Submission.NK.CFTLib.ARL.AuxField
import Submission.NK.CFTLib.ARL.cyclotomicCellKernelLe_B
import Submission.NK.CFTLib.ARLAlt.CellAtAux
import Submission.NK.CFTLib.ARLAlt.Descent
import Submission.NK.CFTLib.ARLAlt.AuxLocal
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSym_restrict_relNorm
import Submission.NK.CFTLib.ArtinReciprocityIdeal.artinSym_restrict_relNorm_of_normal
import Submission.NK.CFTLib.ArtinReciprocityIdeal.norm_principalRay_le
import Submission.NK.CFTLib.ArtinReciprocityIdeal.relNormUnit_trans
import Submission.NK.CFTLib.ARL.RelNormFI
import Submission.NK.CFTLib.ARL.isGalois_cyclotomicField_over_base
import Submission.NK.CFTLib.ARL.kernelLe_of_auxField_B
import Submission.NK.Existence.ArtinLemma.helpers
import Submission.NK.Chebotarev.IsFrobAtPrimeAlgEquivSameBase
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors IsMulCommutative

noncomputable section

namespace NK.CFTLib.ArtinReciprocityIdeal

/-! ## Auxiliary lemmas for the transfer step of Artin's trick -/



/-- `FracCoprime` is multiplicative. -/
lemma FracCoprime.mul {K : Type} [Field K] [NumberField K] {m : ℕ} {A B : Frac K}
    (hA : FracCoprime m A) (hB : FracCoprime m B) : FracCoprime m (A * B) := by
  intro 𝔭 h𝔭
  rw [Units.val_mul, FractionalIdeal.count_mul K 𝔭 (Units.ne_zero A) (Units.ne_zero B),
    hA 𝔭 h𝔭, hB 𝔭 h𝔭, add_zero]

/-- `FracCoprime` is preserved by integer powers. -/
lemma FracCoprime.zpow {K : Type} [Field K] [NumberField K] {m : ℕ} {A : Frac K} (n : ℤ)
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
    NK.CFTLib.ARL.mul_comm_cyclotomicField hcomm M
  have hGalF : ∀ F : IntermediateField K (CyclotomicField M L), IsGalois K ↥F :=
    fun F => NK.CFTLib.ARL.isGalois_intermediateField_cyclotomicField_aux hcomm M F
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
    exact NK.CFTLib.ARL.isMulCommutative_LImage (K := K) (L := L) M
  have hcommLΩ : ∀ a b : Gal(↥LΩ/K), a * b = b * a :=
    fun a b => IsMulCommutative.is_comm.comm a b
  -- ### the isomorphism `↥LΩ ≃ₐ[K] L` and the conjugate generator
  let eL : ↥LΩ ≃ₐ[K] L := hLΩdef ▸ NK.CFTLib.ARLAlt.LImageEquiv (K := K) (L := L) M
  let σΩ : Gal(↥LΩ/K) := NK.CFTLib.ARL.conjHom eL.symm σ
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
    exact hp (NK.CFTLib.ARL.isUnramified_LImage (K := K) (L := L) M m hram p hm_p hM_p)
  -- ### a lift of `σΩ` to `Gal(Ω/↥E)`
  obtain ⟨σ', hσ'⟩ := NK.CFTLib.ARL.restrictNormalHom_comp_restrictScalars_surjective
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
      hLΩdef ▸ NK.CFTLib.ARL.isUnramified_LImage (K := K) (L := L) M m hram 𝔭.1
        (hsmem 𝔭.1 𝔭.2) (hpM 𝔭.1 𝔭.2)
    refine (NK.Chebotarev.isFrobAtPrime_iff_frobAtPrime_eq hcommLΩ 𝔭.1 h𝔭unrΩ _).mp ?_
    have h1 : NK.Chebotarev.IsFrobAtPrime (K := K) (L := L) 𝔭.1 (σ ^ sEx 𝔭.1) := by
      rw [← hsEx 𝔭.1 𝔭.2]
      exact NK.Chebotarev.isFrobAtPrime_frobAtPrime hcomm 𝔭.1 h𝔭unr
    have h2 := (NK.Chebotarev.IsFrobAtPrimeAlgEquivSameBase (K := K) eL.symm
      (σ ^ sEx 𝔭.1) 𝔭.1).mp h1
    rwa [show (AlgEquiv.symm eL).symm.trans ((σ ^ sEx 𝔭.1).trans eL.symm)
        = σΩ ^ sEx 𝔭.1 from
      map_zpow (NK.CFTLib.ARL.conjHom eL.symm) σ (sEx 𝔭.1)] at h2
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
    letI : Algebra ↥(Ef 𝔭) ↥E := NK.CFTLib.ARL.algOfLe (Ef 𝔭) E (hEfle 𝔭)
    haveI : IsScalarTower K ↥(Ef 𝔭) ↥E :=
      NK.CFTLib.ARL.isScalarTower_algOfLe (Ef 𝔭) E (hEfle 𝔭)
    haveI : FiniteDimensional ↥(Ef 𝔭) ↥E :=
      NK.CFTLib.ARL.finiteDimensional_algOfLe (Ef 𝔭) E (hEfle 𝔭)
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
      exact FracCoprime.mul (FracCoprime.zpow _ h𝔓cop) (FracCoprime.zpow _ h𝔠cop)
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
            exact h (NK.CFTLib.ARL.isUnramified_cellAtAux M (Ef 𝔭) (hEfjoin 𝔭) q hMq)
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
      refine le_sup_of_le_right (le_trans ?_ (NK.CFTLib.ARL.normRay_le_of_algEquiv eL.symm m))
      · letI : Algebra ↥LΩ ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭)
            ((Ef 𝔭) ⊔ LΩ) le_sup_left) :=
          NK.CFTLib.ARL.algOfLe LΩ ((Ef 𝔭) ⊔ LΩ) le_sup_right
        haveI : IsScalarTower K ↥LΩ
            ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left) :=
          NK.CFTLib.ARL.isScalarTower_algOfLe LΩ ((Ef 𝔭) ⊔ LΩ) le_sup_right
        haveI : FiniteDimensional ↥LΩ
            ↥(NK.CFTLib.ARLAlt.ofLe (Ef 𝔭) ((Ef 𝔭) ⊔ LΩ) le_sup_left) :=
          NK.CFTLib.ARL.finiteDimensional_algOfLe LΩ ((Ef 𝔭) ⊔ LΩ) le_sup_right
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

end NK.CFTLib.ArtinReciprocityIdeal

end
