import Mathlib.NumberTheory.RamificationInertia.Galois
import Submission.NK.UchidaKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Completely split primes via the local degrees

For a finite Galois extension of number fields `L / K` and a nonzero prime `p` of `𝓞 K`, the
number of primes of `𝓞 L` above `p` equals the degree `[L : K]` exactly when every prime `P` above
`p` has local degree `[L_P : K_p] = e(P|p) · f(P|p)` equal to `1`.

This is the fundamental identity in the Galois case: the primes above `p` all have the same
ramification index and inertia degree (Mathlib's `Ideal.ramificationIdxIn`, `Ideal.inertiaDegIn`),
so that `r · (e · f) = [L : K]` with `r` the number of primes above `p`.  Hence `r = [L : K]`
forces `e · f = 1`, and conversely.
-/

set_option linter.style.haveILetI false

namespace NK.UchidaKummer.API

open IsDedekindDomain

theorem splitsCompletely_iff_forall_localDeg_eq_one
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (p : NK.Chebotarev.PrimeIdeal K) :
    NK.UchidaKummer.SplitsCompletely (K := K) (L := L) p ↔
      ∀ P : NK.Chebotarev.PrimeIdeal L, P.asIdeal.LiesOver p.asIdeal →
        NK.UchidaKummer.localDeg P p = 1 := by
  classical
  constructor
  · intro h P hP
    have h1 :=
      (Commons.NumberTheory.NumberField.ncard_primesOver_eq_finrank_iff_splitCompletely
        (K := K) (L := L) p).mp h
    haveI : P.asIdeal.LiesOver p.asIdeal := hP
    haveI hGal : IsGaloisGroup Gal(L/K) (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L) :=
      IsGaloisGroup.of_isFractionRing Gal(L/K) (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L) K L
    have he := Ideal.ramificationIdxIn_eq_ramificationIdx
      (A := NumberField.RingOfIntegers K) (B := NumberField.RingOfIntegers L)
      p.asIdeal P.asIdeal (Gal(L/K))
    have hf := Ideal.inertiaDegIn_eq_inertiaDeg
      (A := NumberField.RingOfIntegers K) (B := NumberField.RingOfIntegers L)
      p.asIdeal P.asIdeal (Gal(L/K))
    rw [NK.UchidaKummer.localDeg, he.symm, hf.symm, h1.1, h1.2, mul_one]
  · intro h
    obtain ⟨P₀, hP₀⟩ := NK.Chebotarev.exists_primeIdeal_liesOver (K := K) (L := L) p
    haveI : P₀.asIdeal.LiesOver p.asIdeal := hP₀
    haveI hGal : IsGaloisGroup Gal(L/K) (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L) :=
      IsGaloisGroup.of_isFractionRing Gal(L/K) (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L) K L
    have he := Ideal.ramificationIdxIn_eq_ramificationIdx
      (A := NumberField.RingOfIntegers K) (B := NumberField.RingOfIntegers L)
      p.asIdeal P₀.asIdeal (Gal(L/K))
    have hf := Ideal.inertiaDegIn_eq_inertiaDeg
      (A := NumberField.RingOfIntegers K) (B := NumberField.RingOfIntegers L)
      p.asIdeal P₀.asIdeal (Gal(L/K))
    have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
      (A := NumberField.RingOfIntegers K) p.asIdeal (NumberField.RingOfIntegers L) (Gal(L/K))
    rw [IsGalois.card_aut_eq_finrank K L] at hfund
    have hloc := h P₀ hP₀
    rw [NK.UchidaKummer.localDeg] at hloc
    have hprod : p.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers L) *
        p.asIdeal.inertiaDegIn (NumberField.RingOfIntegers L) = 1 := by
      rw [he, hf]; exact hloc
    rw [hprod, mul_one] at hfund
    exact hfund

end NK.UchidaKummer.API
