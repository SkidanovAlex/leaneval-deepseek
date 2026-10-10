import Mathlib
import Submission.Work.MotV5.Nodes.UEPR.valuation_le_one_of_isIntegral
import Submission.Work.MotV5.Nodes.UEPR.subring_eq_range_of_isDiscreteValuationRing_le
import Submission.Work.MotV5.Nodes.UEPR.lt_one_iff
import Submission.Work.MotV5.Nodes.UEPR.integralClosure_le_valuationSubring
import Submission.Work.MotV5.Nodes.UEPR.algebraMap_ofField_range_le

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

-- `haveI` below introduces proposition-valued instances; the style linter misreads these as
-- inlined `have`s.
set_option linter.style.haveILetI false

namespace Work.MotV5.Nodes.UEPR

open scoped WithZero
open IsLocalRing

/-
**The bridge**: any extension `w` of the valuation `v` to the finite Galois extension `Ω` has
valuation ring equal to the localization of the integral closure `B = integralClosure A Ω`
(`A = v.valuationSubring`) at some prime `P = m_w ∩ B` above the maximal ideal `m_A`.

Mathematically this is the standard bijection between extensions of a discrete valuation and primes
of the integral closure; the "hard" direction (`V ⊆ B_P`) follows from the fact that a discrete
valuation ring with fraction field `Ω` is a maximal proper subring of `Ω` (else the uniformiser
inverse lies in `V`, forcing `V = Ω`).

Proof route:
1. `haveI` the DVR/Dedekind instances for `↥A = ↥(v.valuationSubring)` from `hv : v.IsNontrivial`.
2. `hAV : A ≤ w.valuationSubring` from `hsub`; hence `B ⊆ w.valuationSubring` because elements of
   `B` are integral over `↥A` (use `Work.MotV5.Nodes.UEPR.valuation_le_one_of_isIntegral` from
   `Submission.Work.MotV5.Nodes.UEPR.valuation_le_one_of_isIntegral` if that module exists,
   otherwise prove that integrality bound inline).
3. `P := Ideal.comap (Subring.inclusion hBV) (IsLocalRing.maximalIdeal w.valuationSubring)`; it is
   prime, lies over `m_A`, and `P ≠ ⊥`.
4. `Vloc := Localization.subalgebra.ofField Ω P.primeCompl hP`; `IsLocalization P.primeCompl ↥Vloc`,
   `IsFractionRing ↥Vloc Ω`, `IsDiscreteValuationRing ↥Vloc`
   (`IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain` transferred along
   `IsLocalization.algEquiv`).
5. `(algebraMap ↥Vloc Ω).range ≤ w.valuationSubring.toSubring` (elements of the localization are
   `b/s` with `s ∉ P`, so `s ∉ m_w` is a unit of `w.valuationSubring`).
6. `w.valuationSubring.toSubring ≠ ⊤` because `m_A ≠ 0` and `m_A ⊆ m_w`.
7. Conclude with `Work.MotV5.Nodes.UEPR.subring_eq_range_of_isDiscreteValuationRing_le` from
   `Submission.Work.MotV5.Nodes.UEPR.subring_eq_range_of_isDiscreteValuationRing_le` if that
   module exists, otherwise inline that argument (it is short: a DVR `R` with `Frac R = Ω` is a
   maximal proper subring of `Ω`).
-/
theorem bridge {F Ω Γ : Type*} [Field F] [Field Ω] [Algebra F Ω] [FiniteDimensional F Ω] [IsGalois F Ω] (v : Valuation F (WithZero (Multiplicative ℤ))) (hv : v.IsNontrivial) [LinearOrderedCommGroupWithZero Γ] (w : Valuation Ω Γ) (hsub : ∀ x : F, w (algebraMap F Ω x) ≤ 1 ↔ v x ≤ 1) [IsFractionRing ↥(integralClosure ↥(v.valuationSubring) Ω) Ω] : ∃ (P : Ideal ↥(integralClosure ↥(v.valuationSubring) Ω)) (_ : P.IsPrime) (_ : P.LiesOver (IsLocalRing.maximalIdeal ↥(v.valuationSubring))) (hP : P.primeCompl ≤ nonZeroDivisors ↥(integralClosure ↥(v.valuationSubring) Ω)), w.valuationSubring.toSubring = (Localization.subalgebra.ofField Ω P.primeCompl hP).toSubring := by
  classical
  -- ### Step 1: the base valuation ring `A` is a discrete valuation ring, hence Dedekind
  haveI := hv
  haveI hAdvr : IsDiscreteValuationRing ↥(v.valuationSubring) := inferInstance
  haveI hAded : IsDedekindDomain ↥(v.valuationSubring) :=
    (IsDiscreteValuationRing.TFAE ↥(v.valuationSubring)
      (isField_iff_maximalIdeal_eq.not.mpr IsDiscreteValuationRing.not_a_field')).out 1 3 |>.mp hAdvr
  -- hence the integral closure `B` is Dedekind
  haveI hBded : IsDedekindDomain ↥(integralClosure ↥(v.valuationSubring) Ω) :=
    IsIntegralClosure.isDedekindDomain ↥(v.valuationSubring) F Ω
      ↥(integralClosure ↥(v.valuationSubring) Ω)
  -- the valuation ring of `w` is local (this instance is needed for the `Subring` formulation)
  haveI hWlocal : IsLocalRing ↥(w.valuationSubring.toSubring) :=
    (inferInstance : IsLocalRing ↥(w.valuationSubring))
  -- ### Step 2: `B ⊆ w.valuationSubring`
  have hBW : (integralClosure ↥(v.valuationSubring) Ω).toSubring ≤ w.valuationSubring.toSubring :=
    integralClosure_le_valuationSubring v w hsub
  -- ### Step 3: the prime `P = m_w ∩ B`
  let P : Ideal ↥(integralClosure ↥(v.valuationSubring) Ω) :=
    Ideal.comap (Subring.inclusion hBW) (IsLocalRing.maximalIdeal (w.valuationSubring.toSubring))
  haveI hPprime : P.IsPrime := Ideal.comap_isPrime _ _
  have hPval : P.primeCompl ≤ nonZeroDivisors ↥(integralClosure ↥(v.valuationSubring) Ω) :=
    Ideal.primeCompl_le_nonZeroDivisors P
  -- `P` lies over `m_A`
  have hPlies : P.LiesOver (IsLocalRing.maximalIdeal ↥(v.valuationSubring)) := by
    refine ⟨Ideal.ext fun a => ?_⟩
    rw [Ideal.mem_under, Ideal.mem_comap]
    have h1 : a ∈ IsLocalRing.maximalIdeal ↥(v.valuationSubring) ↔ v (a : F) < 1 :=
      Valuation.mem_maximalIdeal_iff (K := F) v
    have h2 : (Subring.inclusion hBW (algebraMap ↥(v.valuationSubring)
          ↥(integralClosure ↥(v.valuationSubring) Ω) a)) ∈
        IsLocalRing.maximalIdeal ↥(w.valuationSubring.toSubring) ↔ w (algebraMap F Ω (a : F)) < 1 := by
      have h := Valuation.mem_maximalIdeal_iff (K := Ω) w
        (a := ((Subring.inclusion hBW (algebraMap ↥(v.valuationSubring)
          ↥(integralClosure ↥(v.valuationSubring) Ω) a) : ↥(w.valuationSubring.toSubring)) :
            ↥(w.valuationSubring)))
      have hcoe : (((Subring.inclusion hBW (algebraMap ↥(v.valuationSubring)
          ↥(integralClosure ↥(v.valuationSubring) Ω) a) : ↥(w.valuationSubring.toSubring)) :
            ↥(w.valuationSubring)) : Ω) = algebraMap F Ω (a : F) := by
        rw [Subring.coe_inclusion]
        exact IsScalarTower.algebraMap_apply ↥(v.valuationSubring) F Ω a
      rw [hcoe] at h
      exact h
    exact h1.trans ((lt_one_iff v w hsub (a : F)).symm.trans h2.symm)
  -- ### Step 3bis: `P ≠ ⊥`
  have hinj : Function.Injective (algebraMap ↥(v.valuationSubring)
      ↥(integralClosure ↥(v.valuationSubring) Ω)) := by
    intro x y h
    have h4 : algebraMap ↥(v.valuationSubring) Ω x = algebraMap ↥(v.valuationSubring) Ω y :=
      congrArg (fun z : ↥(integralClosure ↥(v.valuationSubring) Ω) => (z : Ω)) h
    rw [IsScalarTower.algebraMap_apply ↥(v.valuationSubring) F Ω,
        IsScalarTower.algebraMap_apply ↥(v.valuationSubring) F Ω] at h4
    exact Subtype.ext ((algebraMap F Ω).injective h4)
  have hPbot : P ≠ ⊥ := by
    intro hbot
    obtain ⟨a, hamem, hane⟩ := (IsLocalRing.maximalIdeal ↥(v.valuationSubring)).ne_bot_iff.mp
      IsDiscreteValuationRing.not_a_field'
    have hmem : (algebraMap ↥(v.valuationSubring) ↥(integralClosure ↥(v.valuationSubring) Ω) a) ∈ P := by
      rw [← Ideal.mem_under, ← hPlies.over]; exact hamem
    rw [hbot, Ideal.mem_bot] at hmem
    exact hane (hinj (by rw [hmem, map_zero]))
  refine ⟨P, hPprime, hPlies, hPval, ?_⟩
  -- ### Step 4: the localization of `B` at `P`, inside `Ω`, is a discrete valuation ring
  haveI hPloc : IsLocalization.AtPrime ↥(Localization.subalgebra.ofField Ω P.primeCompl hPval) P :=
    Localization.subalgebra.isLocalization_ofField Ω P.primeCompl hPval
  haveI hPdom : IsDomain ↥(Localization.subalgebra.ofField Ω P.primeCompl hPval) :=
    IsLocalization.isDomain_of_atPrime _ P
  haveI hPdvr : IsDiscreteValuationRing ↥(Localization.subalgebra.ofField Ω P.primeCompl hPval) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      ↥(integralClosure ↥(v.valuationSubring) Ω) hPbot _
  haveI hPfrac : IsFractionRing ↥(Localization.subalgebra.ofField Ω P.primeCompl hPval) Ω := inferInstance
  -- ### Step 5: the localization is contained in the valuation ring of `w`
  have hBW' : (algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω).range ≤
      w.valuationSubring.toSubring := by
    rintro x ⟨y, rfl⟩
    exact hBW y.2
  have hunit : ∀ s : P.primeCompl, ∃ u : (w.valuationSubring.toSubring)ˣ,
      ((u : w.valuationSubring.toSubring) : Ω) = algebraMap ↥(integralClosure ↥(v.valuationSubring) Ω) Ω
        (s : ↥(integralClosure ↥(v.valuationSubring) Ω)) := by
    rintro ⟨s, hs⟩
    have hs' : (Subring.inclusion hBW) s ∉ IsLocalRing.maximalIdeal ↥(w.valuationSubring.toSubring) :=
      fun h => hs (Ideal.mem_comap.mpr h)
    have hu : IsUnit ((Subring.inclusion hBW) s) := by
      by_contra hnot
      exact hs' ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnot))
    obtain ⟨u, hu'⟩ := hu
    exact ⟨u, by rw [hu', Subring.coe_inclusion]; rfl⟩
  have hrange := algebraMap_ofField_range_le P hPval w.valuationSubring.toSubring hBW' hunit
  -- ### Step 6: the valuation ring of `w` is a proper subring of `Ω`
  have hne : w.valuationSubring.toSubring ≠ ⊤ := by
    intro htop
    obtain ⟨x, hx⟩ := Valuation.IsNontrivial.exists_one_lt (v := v)
    have hle : w (algebraMap F Ω x) ≤ 1 := by
      have hmem : algebraMap F Ω x ∈ w.valuationSubring.toSubring := by
        rw [htop]; exact Subring.mem_top _
      exact (Valuation.mem_valuationSubring_iff w _).mp hmem
    exact absurd hx (not_lt_of_ge ((hsub x).mp hle))
  -- ### Step 7: a DVR with fraction field `Ω` is a maximal proper subring
  have hfin := subring_eq_range_of_isDiscreteValuationRing_le
    (R := ↥(Localization.subalgebra.ofField Ω P.primeCompl hPval)) (Ω := Ω)
    w.valuationSubring.toSubring hrange hne
  rw [hfin]
  exact Subring.ext fun x => ⟨fun ⟨y, hy⟩ => hy ▸ y.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

end Work.MotV5.Nodes.UEPR
