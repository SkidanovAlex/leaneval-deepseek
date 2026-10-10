import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.NK.CFTLib.HRdescent.localBaseChangeCyclotomicUnramified
import Submission.NK.CFTLib.IdeleHasse.Descent.dvd_localDegree_of_isPrimitiveRoot
import Submission.NK.CFTLib.IdeleHasse.Descent.localConditionArith
import Submission.NK.CFTLib.IdeleHasse.HilbertReciprocityCyclicProof.localCondition_exists_infinite

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.CFTLib.HRdescent

/-- The norm of a height-one prime of a number field is at least `2`. -/
private lemma two_le_absNorm {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    2 ≤ Ideal.absNorm Q.asIdeal := by
  have h0 : Ideal.absNorm Q.asIdeal ≠ 0 :=
    fun hc => Q.ne_bot (Ideal.absNorm_eq_zero_iff.mp hc)
  have h1 : Ideal.absNorm Q.asIdeal ≠ 1 :=
    fun hc => Q.isMaximal.ne_top (Ideal.absNorm_eq_one_iff.mp hc)
  omega

/-- If a rational prime lies in the height-one prime `Q`, then it divides `absNorm Q`. -/
private lemma prime_dvd_absNorm_of_mem {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (l : ℕ) (hl : l.Prime) (h : (l : NumberField.RingOfIntegers K) ∈ Q.asIdeal) :
    l ∣ Ideal.absNorm Q.asIdeal := by
  have hle : Ideal.span ({(l : NumberField.RingOfIntegers K)} : Set (NumberField.RingOfIntegers K))
      ≤ Q.asIdeal := by
    rw [Ideal.span_singleton_le_iff_mem]; exact h
  have hdvd : Ideal.absNorm Q.asIdeal ∣
      Ideal.absNorm (Ideal.span ({(l : NumberField.RingOfIntegers K)} :
        Set (NumberField.RingOfIntegers K))) :=
    Ideal.absNorm_dvd_absNorm_of_le hle
  rw [Ideal.absNorm_span_natCast] at hdvd
  obtain ⟨p, hp, hpdvd⟩ :=
    Nat.exists_prime_and_dvd (n := Ideal.absNorm Q.asIdeal) (by have := two_le_absNorm Q; omega)
  have hpl : p ∣ l := hp.dvd_of_dvd_pow (hpdvd.trans hdvd)
  have hpq : p = l := (hl.eq_one_or_self_of_dvd p hpl).resolve_left hp.ne_one
  exact hpq ▸ hpdvd

/-- The order of the unit `N mod l` is the order of `N` in `ZMod l`. -/
private lemma orderOf_unitOfCoprime_eq {l N : ℕ} (h : N.Coprime l) :
    orderOf (ZMod.unitOfCoprime N h) = orderOf ((N : ZMod l)) := by
  rw [← orderOf_units (y := ZMod.unitOfCoprime N h), ZMod.coe_unitOfCoprime]

theorem localConditionCyclotomicPrimeOdd {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcyc : IsCyclic (L ≃ₐ[K] L)) (v₀ : NK.GlobalCFT.Place K) :
    ∃ (M E : Type) (_ : Field M) (_ : NumberField M) (_ : Field E) (_ : NumberField E)
      (_ : Algebra K M) (_ : Algebra K E) (_ : Algebra L E) (_ : Algebra M E)
      (_ : IsScalarTower K L E) (_ : IsScalarTower K M E)
      (_ : FiniteDimensional K M) (_ : FiniteDimensional K E)
      (_ : IsGalois K M) (_ : IsGalois K E) (_ : IsCyclic (M ≃ₐ[K] M))
      (m : ℕ) (_ : m.Prime) (_ : 2 < m) (_ : IsCyclotomicExtension {m} K M),
      (Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤) ∧
      (∀ (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        v₀ = NK.GlobalCFT.Place.ofFinite Q →
          (m : NumberField.RingOfIntegers K) ∉ Q.asIdeal) ∧
      (∀ (x : Kˣ) (w : NK.GlobalCFT.Place M), NK.GlobalCFT.Place.LiesOver w v₀ →
        Units.map (algebraMap M (NK.GlobalCFT.Place.localField M w)).toMonoidHom
          (Units.map (algebraMap K M).toMonoidHom x) ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := M) (L := E) w) := by
  classical
  rcases v₀ with winf | Q
  · -- ## the archimedean case: `M` of prime conductor `q > 2` is totally complex
    obtain ⟨M, E, hMf, hMN, hEf, hEN, hKM, hKE, hLE, hME, hstLE, hstME, hfdM, hfdE,
      hgalM, hgalE, hcycM, q, hq, hq2, hcycExt, hgen, hloc⟩ :=
      NK.CFTLib.IdeleHasse.HilbertReciprocityCyclicProof.localCondition_exists_infinite
        (K := K) (L := L) hcyc winf
    refine ⟨M, E, hMf, hMN, hEf, hEN, hKM, hKE, hLE, hME, hstLE, hstME, hfdM, hfdE,
      hgalM, hgalE, hcycM, q, hq, hq2, hcycExt, hgen, ?_, hloc⟩
    intro Q' hQ'
    exact absurd hQ' (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite winf Q')
  · -- ## the nonarchimedean case
    have hN2 : 1 < Ideal.absNorm Q.asIdeal := by have := two_le_absNorm Q; omega
    obtain ⟨l, hl, hlt, hdvdord⟩ :=
      NK.CFTLib.IdeleHasse.Descent.exists_prime_gt_orderOf_dvd (Ideal.absNorm Q.asIdeal) hN2
        (Module.finrank K L) Module.finrank_pos
    have hl2 : 2 < l := by have := two_le_absNorm Q; omega
    have hcop : Nat.Coprime (Ideal.absNorm Q.asIdeal) l := by
      have hndvd : ¬ l ∣ Ideal.absNorm Q.asIdeal := by
        intro hd
        have := Nat.le_of_dvd (by have := two_le_absNorm Q; omega) hd
        omega
      exact (hl.coprime_iff_not_dvd.mpr hndvd).symm
    have hlQ : (l : NumberField.RingOfIntegers K) ∉ Q.asIdeal := by
      intro hmem
      have hd : l ∣ Ideal.absNorm Q.asIdeal := prime_dvd_absNorm_of_mem Q l hl hmem
      have h1 : l ∣ Nat.gcd (Ideal.absNorm Q.asIdeal) l := Nat.dvd_gcd hd (dvd_refl l)
      rw [hcop.gcd_eq_one] at h1
      exact hl.not_dvd_one h1
    obtain ⟨M, E, hMf, hMN, hEf, hEN, hKM, hKE, hLE, hME, hstLE, hstME, hfdM, hfdE,
      hgalM, hgalE, hcycM, hcycExt, hgen, heridiv⟩ :=
      NK.CFTLib.IdeleHasse.Crux.cyclotomicAuxiliary (K := K) (L := L) l hl Q hcop
    letI : Algebra K M := hKM
    letI : Algebra K E := hKE
    letI : Algebra L E := hLE
    letI : Algebra M E := hME
    letI : IsScalarTower K L E := hstLE
    letI : IsScalarTower K M E := hstME
    letI : FiniteDimensional K M := hfdM
    letI : FiniteDimensional K E := hfdE
    letI : IsGalois K M := hgalM
    letI : IsGalois K E := hgalE
    letI : IsCyclic (M ≃ₐ[K] M) := hcycM
    letI : IsCyclotomicExtension {l} K M := hcycExt
    haveI : NeZero l := ⟨hl.ne_zero⟩
    -- `M / K` is unramified at `Q`
    have hunr : Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers M) = 1 := by
      obtain ⟨P, hP⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := M) Q
      rw [Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
        (B := NumberField.RingOfIntegers M) Q.asIdeal P.asIdeal (Gal(M/K))]
      exact NK.NUV2.ARL.Gap.isUnramified_cyclotomicExtension (n := l) Q hlQ P hP
    have hdvdunit : Module.finrank K L ∣
        orderOf (ZMod.unitOfCoprime (Ideal.absNorm Q.asIdeal) hcop) := by
      rw [orderOf_unitOfCoprime_eq hcop]; exact hdvdord
    refine ⟨M, E, hMf, hMN, hEf, hEN, hKM, hKE, hLE, hME, hstLE, hstME, hfdM, hfdE,
      hgalM, hgalE, hcycM, l, hl, hl2, hcycExt, hgen, ?_, ?_⟩
    · -- the modulus `l` is prime to `Q`
      intro Q' hQ'
      rw [NK.GlobalCFT.Place.ofFinite_inj] at hQ'
      subst hQ'
      exact hlQ
    · -- the local condition at the places above `Q`
      intro x w hw
      rcases (NK.GlobalCFT.Place.liesOver_iff w (NK.GlobalCFT.Place.ofFinite Q)).mp hw with
        ⟨w', v', hw1, hw2, -⟩ | ⟨q, Q', hw1, hw2, hlo⟩
      · exact absurd hw2 (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite v' Q).symm
      · rw [NK.GlobalCFT.Place.ofFinite_inj] at hw2
        subst hw2
        subst hw1
        have hdvd : Module.finrank K L ∣ q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
          dvd_trans hdvdunit (heridiv q hlo)
        obtain ⟨qc, hqc, hc⟩ :=
          localBaseChangeCyclotomicUnramified (K := K) (L := L) (M := M) (E := E)
            hgen hcyc Q q hlo hunr hdvd
        rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofFinite]
        exact Subgroup.mem_iSup_of_mem ⟨qc, hqc⟩ (hc x)

end NK.CFTLib.HRdescent
