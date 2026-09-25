/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The counting of the primes of a subfield by the orbits of a Frobenius

This file proves the place-indexed form `NK.WeakNU.PrimeCountOrbitInputPlace` of the counting
input of the Perlis/Gassmann step, and reduces the natural-prime-indexed form
`NK.WeakNU.PrimeCountOrbitInput` to it.  The four ingredients are

* `NK.WeakNU.primeCountAbove_eq_primeOrbitCount` — the primes of `N^H` above a place are the
  `H`-orbits of the primes of `N` above it;
* `NK.WeakNU.primeOrbitCount_eq_card_orbits_coset` — the primes of `N` above a place are the
  coset space `Gal(N/ℚ) ⧸ D` of the decomposition subgroup;
* `NK.WeakNU.card_orbits_coset_comm` — the symmetry of double cosets;
* `NK.WeakNU.decompositionSubgroup_eq_zpowers_of_isFrobAt` — for an unramified prime over which
  `σ` is a Frobenius element, the decomposition subgroup is `⟨σ⟩`.

Together with `NK.WeakNU.primeCountAbove_under_eq_primesOverRat`, which identifies the count over
a rational prime `p` with the count over the place of `ℚ` below it, this removes
`PrimeCountOrbitInput` from the residual catalogue of the chapter.
-/

import Submission.NK.WeakNU.PrimeOrbit
import Submission.NK.WeakNU.primeCountAbove_eq_primeOrbitCount
import Submission.NK.WeakNU.primeOrbitCount_eq_card_orbits_coset
import Submission.NK.WeakNU.card_orbits_coset_comm
import Submission.NK.WeakNU.decompositionSubgroup_eq_zpowers_of_isFrobAt
import Submission.NK.WeakNU.primeCountAbove_under_eq_primesOverRat
import Submission.NK.WeakNU.PerlisGassmann

namespace NK.WeakNU

noncomputable section

/-- **The counting of the primes of a subfield by the orbits of a Frobenius**, place-indexed form.

The chain of identifications is

`#(primes of M over 𝔭) = #(Gal(N/M)-orbits of primes over 𝔭) = #(H-orbits on G ⧸ D_𝔓)
  = #(D_𝔓-orbits on G ⧸ H) = #(⟨σ⟩-orbits on G ⧸ H) = orbitCount σ (G ⧸ H)`. -/
theorem primeCountOrbitInputPlace : PrimeCountOrbitInputPlace := by
  intro N _f _nf _alg _gal M 𝔭 _hram σ ⟨P, hP, hfrob⟩
  calc primeCountAbove M 𝔭
      = primeOrbitCount M.fixingSubgroup 𝔭 := primeCountAbove_eq_primeOrbitCount M 𝔭
    _ = Nat.card (MulAction.orbitRel.Quotient M.fixingSubgroup
          (Gal(N/ℚ) ⧸ Submission.NeukirchUchida.Local.decompositionSubgroup (K := ℚ) P)) :=
          primeOrbitCount_eq_card_orbits_coset M.fixingSubgroup 𝔭 P hP
    _ = Nat.card (MulAction.orbitRel.Quotient
          (Submission.NeukirchUchida.Local.decompositionSubgroup (K := ℚ) P)
          (Gal(N/ℚ) ⧸ M.fixingSubgroup)) :=
          (card_orbits_coset_comm M.fixingSubgroup
            (Submission.NeukirchUchida.Local.decompositionSubgroup (K := ℚ) P)).symm
    _ = orbitCount σ (Gal(N/ℚ) ⧸ M.fixingSubgroup) := by
          rw [decompositionSubgroup_eq_zpowers_of_isFrobAt P σ
            (hram := _hram P hP) (hfrob := hfrob)]
          rfl

/-- **The counting input `PrimeCountOrbitInput` from its place-indexed form.**

The only content is the bridge between the rational prime `p` and the place of `ℚ` below a prime `P`
of `𝓞 N` lying over `(p)`
(`NK.WeakNU.primeCountAbove_under_eq_primesOverRat`), together with the transitivity of
`Ideal.under`. -/
theorem primeCountOrbitInput_of_place (h : PrimeCountOrbitInputPlace) : PrimeCountOrbitInput := by
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
  rw [← primeCountAbove_under_eq_primesOverRat M p P hP]
  exact hmain

/-- **The counting input `PrimeCountOrbitInput` is a theorem.**

This is the content of the two lemmas above: the place-indexed counting statement is proved from
the four classical ingredients, and the bridge to the natural-prime-indexed form is
`primeCountAbove_under_eq_primesOverRat`.  Consequently `PrimeCountOrbitInput` is no longer an
input of the Perlis/Gassmann reduction. -/
theorem primeCountOrbitInput : PrimeCountOrbitInput :=
  primeCountOrbitInput_of_place primeCountOrbitInputPlace

/-- **The Perlis/Gassmann input of §6 from Čebotarev's theorem alone.**

Since `PrimeCountOrbitInput` is now a theorem, the only arithmetic input of the Perlis/Gassmann step
is Čebotarev's density theorem.  Perlis' proof by Dedekind zeta functions is replaced by
Čebotarev plus the group-theoretic inversion
`NK.WeakNU.fixedCount_eq_of_orbitCount_eq`. -/
theorem perlisGassmannInput_of_chebotarev (hC : ChebotarevFrobeniusInput) :
    NK.UchidaKummer.PerlisGassmannInput :=
  perlisGassmannInput_of_chebotarev_and_primeCount hC primeCountOrbitInput

end

end NK.WeakNU
