import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.NK.CFTLib.HR.isCyclotomic_onePlace_real
import Submission.NK.CFTLib.IdeleHasse.Descent.cyclotomicLocalDegree
import Submission.NK.CFTLib.IdeleHasse.Descent.localConditionArith
import Submission.NK.CFTLib.IdeleHasse.HilbertReciprocityCyclicProof.localCondition_exists_infinite
import Submission.NK.KC.localBaseChangeInput_of_kc

/-!
# The local condition at a prescribed place, at a cyclotomic prime level

For a cyclic extension `L/K` of number fields and a place `v₀` of `K` we produce a prime `m`, a
cyclotomic level `M = K(ζ_m)` (cyclic over `K`, unramified above `v₀`) and the compositum
`E = L·M` such that at every place of `M` above `v₀` the image of every `x ∈ Kˣ` is a local norm
from `E` — the arithmetic input `hv₀` of the Brauer descent of Hilbert reciprocity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace NK.CFTLib.HRdescent

section Helpers

variable {K L : Type*}

/-- The absolute norm of a nonzero prime of the ring of integers is at least `2`. -/
theorem two_le_absNorm [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    2 ≤ Ideal.absNorm Q.asIdeal := by
  have h0 : Ideal.absNorm Q.asIdeal ≠ 0 := fun hc => Q.ne_bot (Ideal.absNorm_eq_zero_iff.mp hc)
  have h1 : Ideal.absNorm Q.asIdeal ≠ 1 :=
    fun hc => Q.isMaximal.ne_top (Ideal.absNorm_eq_one_iff.mp hc)
  omega

/-- **The local ramification index at `w | Q` is the ramification index of `Q` in `M`.** -/
theorem ramificationIdx_eq_ramificationIdxIn [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hw : w.asIdeal.LiesOver Q.asIdeal) :
    w.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) =
      Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) := by
  letI : MulSemiringAction Gal(L/K) (NumberField.RingOfIntegers L) :=
    IsIntegralClosure.MulSemiringAction (NumberField.RingOfIntegers K) K L
      (NumberField.RingOfIntegers L)
  haveI hGal : IsGaloisGroup Gal(L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L) K L
  exact (Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
    (B := NumberField.RingOfIntegers L) Q.asIdeal w.asIdeal (Gal(L/K))).symm

/-- **The order of `N mod q` is the order of `N` in `ZMod q`.** -/
theorem orderOf_unitOfCoprime_eq {l N : ℕ} (h : N.Coprime l) :
    orderOf (ZMod.unitOfCoprime N h) = orderOf ((N : ZMod l)) := by
  rw [← orderOf_units (y := ZMod.unitOfCoprime N h), ZMod.coe_unitOfCoprime]

/-- **The local degree divides the global degree.** -/
theorem finrank_adicCompletion_dvd_finrank [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (r : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hr : r.asIdeal.LiesOver Q.asIdeal) :
    Module.finrank (Q.adicCompletion K) (r.adicCompletion L) ∣ Module.finrank K L := by
  haveI hgal : IsGalois (Q.adicCompletion K) (r.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.isGalois_adicCompletion Q r hr
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (r.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q r hr
  have h1 : Module.finrank (Q.adicCompletion K) (r.adicCompletion L) =
      Nat.card ↥(Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) r) := by
    rw [← IsGalois.card_aut_eq_finrank (Q.adicCompletion K) (r.adicCompletion L)]
    exact Nat.card_congr (Commons.NumberTheory.NumberField.Completion.decompositionSubgroupMulEquivLocalGalois
      Q r hr).toEquiv.symm
  rw [h1]
  calc Nat.card ↥(Commons.NumberTheory.NumberField.Completion.decompositionSubgroup (K := K) r)
      ∣ Nat.card (L ≃ₐ[K] L) := Subgroup.card_subgroup_dvd_card _
    _ = Module.finrank K L := IsGalois.card_aut_eq_finrank K L

/-- **The local degree of an unramified completion is the inertia degree.** -/
theorem finrank_adicCompletion_eq_inertiaDeg_of_ramificationIdx_eq_one [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hw : w.asIdeal.LiesOver Q.asIdeal)
    (hunr : w.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1) :
    Module.finrank (Q.adicCompletion K) (w.adicCompletion L) =
      w.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) := by
  have h := Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
    Q w hw
  rw [hunr, one_mul] at h
  exact h.symm

end Helpers

/-- **The local condition at a prescribed place, at a cyclotomic prime level.**

For a cyclic extension `L/K` of number fields and any place `v₀` of `K` there are a prime `m`, a
cyclotomic level `M = K(ζ_m)` (Galois and cyclic over `K`) and the compositum `E = L·M` such that
`m` is a unit at the places of `K` above `v₀` and every `x ∈ Kˣ` is a local norm from `E` over `M`
at every place of `M` above `v₀`. -/
theorem localConditionCyclotomicPrime {K L : Type} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hcyc : IsCyclic (L ≃ₐ[K] L)) (v₀ : NK.GlobalCFT.Place K) :
    ∃ (M E : Type) (_ : Field M) (_ : NumberField M) (_ : Field E) (_ : NumberField E)
      (_ : Algebra K M) (_ : Algebra K E) (_ : Algebra L E) (_ : Algebra M E)
      (_ : IsScalarTower K L E) (_ : IsScalarTower K M E)
      (_ : FiniteDimensional K M) (_ : FiniteDimensional K E)
      (_ : IsGalois K M) (_ : IsGalois K E) (_ : IsCyclic (M ≃ₐ[K] M))
      (m : ℕ) (_ : 0 < m) (_ : IsCyclotomicExtension {m} K M),
      (Algebra.adjoin K (Set.range (algebraMap L E) ∪ Set.range (algebraMap M E)) = ⊤) ∧
      (∀ (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
        v₀ = NK.GlobalCFT.Place.ofFinite Q →
          (m : NumberField.RingOfIntegers K) ∉ Q.asIdeal) ∧
      (∀ (x : Kˣ) (w : NK.GlobalCFT.Place M), NK.GlobalCFT.Place.LiesOver w v₀ →
        Units.map (algebraMap M (NK.GlobalCFT.Place.localField M w)).toMonoidHom
          (Units.map (algebraMap K M).toMonoidHom x) ∈
          NK.CFTLib.IdeleHasse.localNormSubgroup (K := M) (L := E) w) := by
  classical
  rcases v₀ with w₀ | Q
  · -- ## the archimedean case: `M` of odd prime conductor is totally complex
    obtain ⟨M, E, hMf, hMN, hEf, hEN, hKM, hKE, hLE, hME, hstLE, hstME, hfdM, hfdE, hgalM,
      hgalE, hcycM, q, hq, _hq2, hcycExt, hgen, hloc⟩ :=
      NK.CFTLib.IdeleHasse.HilbertReciprocityCyclicProof.localCondition_exists_infinite
        (K := K) (L := L) hcyc w₀
    exact ⟨M, E, hMf, hMN, hEf, hEN, hKM, hKE, hLE, hME, hstLE, hstME, hfdM, hfdE, hgalM,
      hgalE, hcycM, q, hq.pos, hcycExt, hgen,
      (fun Q' hQ' => absurd hQ' (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w₀ Q')), hloc⟩
  · -- ## the nonarchimedean case
    obtain ⟨l, hl, hlt, hdvdord⟩ :=
      NK.CFTLib.IdeleHasse.Descent.exists_prime_gt_orderOf_dvd (Ideal.absNorm Q.asIdeal)
        (two_le_absNorm Q) (Module.finrank K L) Module.finrank_pos
    have hndvd : ¬ l ∣ Ideal.absNorm Q.asIdeal := by
      intro hd
      have hpos : 0 < Ideal.absNorm Q.asIdeal :=
        Nat.pos_of_ne_zero fun hc => Q.ne_bot (Ideal.absNorm_eq_zero_iff.mp hc)
      have h2 : l ≤ Ideal.absNorm Q.asIdeal := Nat.le_of_dvd hpos hd
      omega
    have hcop : Nat.Coprime (Ideal.absNorm Q.asIdeal) l :=
      (hl.coprime_iff_not_dvd.mpr hndvd).symm
    -- the prime `l` is a unit at `Q`
    have hlQ : (l : NumberField.RingOfIntegers K) ∉ Q.asIdeal := by
      intro hmem
      have hle : Ideal.span ({(l : NumberField.RingOfIntegers K)} :
          Set (NumberField.RingOfIntegers K)) ≤ Q.asIdeal := by
        rw [Ideal.span_singleton_le_iff_mem]; exact hmem
      have hdvd : Ideal.absNorm Q.asIdeal ∣ Ideal.absNorm
          (Ideal.span ({(l : NumberField.RingOfIntegers K)} :
            Set (NumberField.RingOfIntegers K))) :=
        Ideal.absNorm_dvd_absNorm_of_le hle
      rw [Ideal.absNorm_span_natCast] at hdvd
      obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd
        (n := Ideal.absNorm Q.asIdeal) (by have := two_le_absNorm Q; omega)
      have hpl_pow : p ∣ l ^ Module.finrank ℤ (NumberField.RingOfIntegers K) :=
        hpdvd.trans hdvd
      have hpl : p ∣ l := hp.dvd_of_dvd_pow hpl_pow
      have hpq : p = l := (hl.eq_one_or_self_of_dvd p hpl).resolve_left hp.ne_one
      have hlabs : l ∣ Ideal.absNorm Q.asIdeal := hpq ▸ hpdvd
      exact hl.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hlabs (dvd_refl l))
    -- the cyclotomic auxiliary field
    obtain ⟨M, E, hMf, hMN, hEf, hEN, hKM, hKE, hLE, hME, hstLE, hstME, hfdM, hfdE, hgalM,
      hgalE, hcycM, hcycExt, hgen, heridiv⟩ :=
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
    have hdivord : Module.finrank K L ∣
        orderOf (ZMod.unitOfCoprime (Ideal.absNorm Q.asIdeal) hcop) := by
      rw [orderOf_unitOfCoprime_eq hcop]
      exact hdvdord
    refine ⟨M, E, hMf, hMN, hEf, hEN, hKM, hKE, hLE, hME, hstLE, hstME, hfdM, hfdE, hgalM,
      hgalE, hcycM, l, hl.pos, hcycExt, hgen, ?_, ?_⟩
    · -- ## the conductor is a unit at `Q`
      intro Q' hQ'
      have hQQ' : Q = Q' := NK.GlobalCFT.Place.ofFinite_inj.mp hQ'
      rw [← hQQ']
      exact hlQ
    · -- ## the local condition at every place above `Q`
      intro x w hw
      rcases hw with ⟨w', v', hw1, hw2, _hlo⟩ | ⟨q', Q', hw1, hw2, hq'Q'⟩
      · exact absurd hw2.symm (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite v' Q)
      · have hQ'Q : Q = Q' := NK.GlobalCFT.Place.ofFinite_inj.mp hw2
        subst hw1
        rw [← hQ'Q] at hq'Q'
        have hunr : Q.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers M) = 1 := by
          have h := (NK.CFTLib.IdeleHasse.Descent.cyclotomicLocalDegree Q l hl hlQ q'
            hq'Q').1
          rw [← ramificationIdx_eq_ramificationIdxIn Q q' hq'Q']
          exact h
        have hdiv : Module.finrank K L ∣
            q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
          hdivord.trans (heridiv q' hq'Q')
        have hloc : ∀ (r : IsDedekindDomain.HeightOneSpectrum
              (NumberField.RingOfIntegers L))
            (hr : r.asIdeal.LiesOver Q.asIdeal),
            Module.finrank (Q.adicCompletion K) (r.adicCompletion L) ∣
              Module.finrank (Q.adicCompletion K) (q'.adicCompletion M) := by
          intro r hr
          have hMw : Module.finrank (Q.adicCompletion K) (q'.adicCompletion M) =
              q'.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) :=
            finrank_adicCompletion_eq_inertiaDeg_of_ramificationIdx_eq_one Q q' hq'Q'
              (NK.CFTLib.IdeleHasse.Descent.cyclotomicLocalDegree Q l hl hlQ q' hq'Q').1
          rw [hMw]
          exact (finrank_adicCompletion_dvd_finrank Q r hr).trans hdiv
        obtain ⟨q'', hq'', hcond⟩ :=
          NK.KC.localBaseChangeInput_of_kc (K := K) (L := L) (M := M) (E := E)
            hgen hcyc Q q' hq'Q' hunr hloc
        rw [NK.CFTLib.IdeleHasse.localNormSubgroup_ofFinite (K := M) (L := E) q']
        exact Subgroup.mem_iSup_of_mem ⟨q'', hq''⟩ (hcond x)

end NK.CFTLib.HRdescent
