/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Perlis/Gassmann input at an arbitrary universe

Universe-polymorphic copies of the reduction of `Submission/Work/WeakNU/`:

* `NK.UniverseWeakNU.primeCountOrbitInputPlaceU` — the place-indexed counting statement, from
  the four universe-polymorphic ingredients `primeCountAboveU_eq_primeOrbitCountU`,
  `primeOrbitCountU_eq_card_orbits_cosetU`, `NK.WeakNU.card_orbits_coset_comm` (pure group
  theory, already polymorphic) and `decompositionSubgroup_eq_zpowers_of_isFrobAtU`;
* `NK.UniverseWeakNU.primeCountOrbitInputU` — its natural-prime-indexed form, via
  `primeCountAboveU_under_eq_primesOverRatU`;
* `NK.UniverseWeakNU.perlisGassmannInputU_of_chebotarev_and_primeCountU` and
  `NK.UniverseWeakNU.perlisGassmannInputU` — the Perlis/Gassmann step, from Čebotarev's theorem
  alone (the counting statement being a theorem here).

The two group-theoretic lemmas of the inversion,
`NK.WeakNU.fixedCount_eq_of_orbitCount_eq` and
`NK.WeakNU.exists_conj_mem_of_fixedCount_coset_eq`, are already universe-polymorphic
(`{G : Type*}`, `{X : Type*}`, …; the `Prop` they concern, `NK.WeakNU.orbitCount` /
`NK.WeakNU.fixedCount`, is that of `WeakNU/Defs.lean`), so they are used here directly rather
than copied.
-/

import Mathlib
import Submission.NK.UniverseWeakNU.Defs
import Submission.NK.UniverseWeakNU.PrimeOrbitU
import Submission.NK.UniverseWeakNU.primeCountAboveU_eq_primeOrbitCountU
import Submission.NK.UniverseWeakNU.primeOrbitCountU_eq_card_orbits_cosetU
import Submission.NK.UniverseWeakNU.decompositionSubgroup_eq_zpowers_of_isFrobAtU
import Submission.NK.UniverseWeakNU.primeCountAboveU_under_eq_primesOverRatU
import Submission.NK.WeakNU.fixedCount_eq_of_orbitCount_eq
import Submission.NK.WeakNU.exists_conj_mem_of_fixedCount_coset_eq
import Submission.NK.WeakNU.card_orbits_coset_comm

namespace NK.UniverseWeakNU

noncomputable section

universe u

/-- **The counting of the primes of a subfield by the orbits of a Frobenius**, place-indexed form,
at an arbitrary universe.  Copy of `NK.WeakNU.primeCountOrbitInputPlace`. -/
theorem primeCountOrbitInputPlaceU : PrimeCountOrbitInputPlaceU.{u} := by
  intro N _f _nf _alg _gal M 𝔭 _hram σ ⟨P, hP, hfrob⟩
  calc primeCountAbove M 𝔭
      = primeOrbitCount M.fixingSubgroup 𝔭 := primeCountAboveU_eq_primeOrbitCountU M 𝔭
    _ = Nat.card (MulAction.orbitRel.Quotient M.fixingSubgroup
          (Gal(N/ℚ) ⧸ Submission.NeukirchUchida.Local.decompositionSubgroup (K := ℚ) P)) :=
          primeOrbitCountU_eq_card_orbits_cosetU M.fixingSubgroup 𝔭 P hP
    _ = Nat.card (MulAction.orbitRel.Quotient
          (Submission.NeukirchUchida.Local.decompositionSubgroup (K := ℚ) P)
          (Gal(N/ℚ) ⧸ M.fixingSubgroup)) :=
          (NK.WeakNU.card_orbits_coset_comm M.fixingSubgroup
            (Submission.NeukirchUchida.Local.decompositionSubgroup (K := ℚ) P)).symm
    _ = NK.WeakNU.orbitCount σ (Gal(N/ℚ) ⧸ M.fixingSubgroup) := by
          rw [decompositionSubgroup_eq_zpowers_of_isFrobAtU P σ (hram := _hram P hP)
            (hfrob := hfrob)]
          rfl

/-- **The counting input `PrimeCountOrbitInputU` from its place-indexed form**, at an arbitrary
universe.  Copy of `NK.WeakNU.primeCountOrbitInput_of_place`. -/
theorem primeCountOrbitInputOfPlaceU (h : PrimeCountOrbitInputPlaceU.{u}) :
    PrimeCountOrbitInputU.{u} := by
  intro N _f _nf _alg _gal M p _hp hram σ ⟨P, hP, hfrob⟩
  have hunder : P.asIdeal.LiesOver
      (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) P).asIdeal := by
    rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
    exact ⟨rfl⟩
  -- a prime above the place `𝔭` below `P` lies above `(p)`, by transitivity of `Ideal.under`
  have hram' : ∀ Q : NK.Chebotarev.PrimeIdeal N,
      Q.asIdeal.LiesOver
        (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) P).asIdeal →
      Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers ℚ) = 1 := by
    intro Q hQ
    apply hram Q
    rw [Ideal.liesOver_iff] at hP hQ ⊢
    calc Ideal.span {↑p}
        = Ideal.under ℤ P.asIdeal := hP
      _ = Ideal.under ℤ (Ideal.under (NumberField.RingOfIntegers ℚ) P.asIdeal) :=
            (Ideal.under_under (A := ℤ) (B := NumberField.RingOfIntegers ℚ) P.asIdeal).symm
      _ = Ideal.under ℤ
            (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers ℚ) P).asIdeal := by
            rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
      _ = Ideal.under ℤ (Ideal.under (NumberField.RingOfIntegers ℚ) Q.asIdeal) := by
            rw [← hQ]
      _ = Ideal.under ℤ Q.asIdeal :=
            Ideal.under_under (A := ℤ) (B := NumberField.RingOfIntegers ℚ) Q.asIdeal
  have hmain := h N M _ hram' σ ⟨P, hunder, hfrob⟩
  rw [← primeCountAboveU_under_eq_primesOverRatU M p P hP]
  exact hmain

/-- **The counting input `PrimeCountOrbitInputU` is a theorem**, at an arbitrary universe. -/
theorem primeCountOrbitInputU : PrimeCountOrbitInputU.{u} :=
  primeCountOrbitInputOfPlaceU primeCountOrbitInputPlaceU

/-- **The Perlis/Gassmann input of §6 from Čebotarev plus the prime count**, at an arbitrary
universe.  Copy of `NK.WeakNU.perlisGassmannInput_of_chebotarev_and_primeCount`. -/
theorem perlisGassmannInputU_of_chebotarev_and_primeCountU
    (hC : ChebotarevFrobeniusInputU.{u}) (hPC : PrimeCountOrbitInputU.{u}) :
    PerlisGassmannInputU.{u} := by
  intro N _f _nf _alg _gal M₁ M₂ hAE
  -- Step 1: the orbit counts of the two coset spaces agree at every element of the Galois group.
  have key : ∀ (A B : IntermediateField ℚ N), NK.UchidaKummer.ArithmeticallyEquivalent ↥A ↥B →
      ∀ σ : Gal(N/ℚ), NK.WeakNU.orbitCount σ (Gal(N/ℚ) ⧸ A.fixingSubgroup) =
        NK.WeakNU.orbitCount σ (Gal(N/ℚ) ⧸ B.fixingSubgroup) := by
    intro A B hAB σ
    obtain ⟨T, hT⟩ := hAB
    obtain ⟨p, hp, hpT, hram, P, hP, hfrob⟩ := hC N σ T
    have h1 := hPC N A p hp hram σ ⟨P, hP, hfrob⟩
    have h2 := hPC N B p hp hram σ ⟨P, hP, hfrob⟩
    have h3 := hT p hp hpT
    exact h1.symm.trans (h3.trans h2)
  -- Step 2 and 3: the fixed-point counts agree, whence the conjugacy-into condition.
  have hfix : ∀ (A B : IntermediateField ℚ N), NK.UchidaKummer.ArithmeticallyEquivalent ↥A ↥B →
      ∀ x ∈ A.fixingSubgroup, ∃ γ : Gal(N/ℚ), γ * x * γ⁻¹ ∈ B.fixingSubgroup := by
    intro A B hAB x hx
    have hfixed : ∀ σ : Gal(N/ℚ), NK.WeakNU.fixedCount σ (Gal(N/ℚ) ⧸ A.fixingSubgroup) =
        NK.WeakNU.fixedCount σ (Gal(N/ℚ) ⧸ B.fixingSubgroup) := by
      intro σ
      exact NK.WeakNU.fixedCount_eq_of_orbitCount_eq σ (fun i => key A B hAB (σ ^ i))
    exact NK.WeakNU.exists_conj_mem_of_fixedCount_coset_eq A.fixingSubgroup B.fixingSubgroup
      hfixed x hx
  exact ⟨hfix M₁ M₂ hAE, hfix M₂ M₁ hAE.symm⟩

/-- **The Perlis/Gassmann input of §6 from Čebotarev's theorem alone**, at an arbitrary universe.
Copy of `NK.WeakNU.perlisGassmannInput_of_chebotarev`. -/
theorem perlisGassmannInputU (hC : ChebotarevFrobeniusInputU.{u}) :
    PerlisGassmannInputU.{u} :=
  perlisGassmannInputU_of_chebotarev_and_primeCountU hC primeCountOrbitInputU

end

end NK.UniverseWeakNU
