import Mathlib
import Submission.NK.UchidaKummer.SplitPrimes
import Submission.NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.SecondInequality.KummerCase

/-- **A prime of `K` splitting completely in `L` outside a prescribed finite set.**

The completely split primes of a finite Galois extension `L / K` of number fields have Dirichlet
density `1 / [L : K] > 0`, while a finite set of primes has density `0`; hence there is a prime of
`K` outside any prescribed finite set `T` which splits completely in `L`, i.e. every prime of `L`
above it is unramified (`e = 1`) of residue degree one (`f = 1`). -/
theorem exists_prime_splitsCompletely_notMem
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    ∃ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K), q ∉ T ∧
      (∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
        Q.asIdeal.LiesOver q.asIdeal →
          Q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1 ∧
          Q.asIdeal.inertiaDeg (NumberField.RingOfIntegers K) = 1) := by
  -- A completely split prime outside the finite set `T`.
  obtain ⟨q, hqT, hsplit⟩ :=
    NK.UchidaKummer.exists_splitsCompletely_notMem (K := K) (L := L) T
  refine ⟨q, hqT, fun Q hQ => ?_⟩
  -- Complete splitting means local degree `e · f = 1` at every prime above `q`.
  have h := (NK.UchidaKummer.API.splitsCompletely_iff_forall_localDeg_eq_one
    (K := K) (L := L) q).mp hsplit Q hQ
  rw [NK.UchidaKummer.localDeg] at h
  exact mul_eq_one.mp h

end NK.GlobalCFTdeep.SecondInequality.KummerCase
