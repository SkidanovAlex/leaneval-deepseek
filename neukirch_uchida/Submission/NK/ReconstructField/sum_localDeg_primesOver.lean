import Mathlib
import Submission.NK.UchidaKummer.Defs

namespace NK.ReconstructField

/-- **The fundamental identity for the local degrees of a relative extension.**

Let `L / K` be a finite extension of number fields and `P` a finite prime of `K`.  Summing the
local degrees `[L_𝔔 : K_𝔓] = e(𝔔|𝔓) · f(𝔔|𝔓)` (`NK.UchidaKummer.localDeg`) over the primes `𝔔`
of `𝓞 L` above `P` gives the global degree `[L : K]`.

This is `Ideal.sum_ramification_inertia_eq_finrank` for the extension `𝓞 L / 𝓞 K`, transported to
the fields by `IsFractionRing.finrank_eq`. -/
theorem sum_localDeg_primesOver {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] (P : NK.Chebotarev.PrimeIdeal K) :
    ∑ Q : P.asIdeal.primesOver (NumberField.RingOfIntegers L),
      NK.UchidaKummer.localDeg
        ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2⟩ P = Module.finrank K L := by
  classical
  have hterm : ∀ Q : P.asIdeal.primesOver (NumberField.RingOfIntegers L),
      NK.UchidaKummer.localDeg ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver P.ne_bot Q.2⟩ P
      = Q.1.ramificationIdx (NumberField.RingOfIntegers K) *
        Q.1.inertiaDeg (NumberField.RingOfIntegers K) := by
    intro Q
    rfl
  trans ∑ Q : P.asIdeal.primesOver (NumberField.RingOfIntegers L),
      Q.1.ramificationIdx (NumberField.RingOfIntegers K) *
        Q.1.inertiaDeg (NumberField.RingOfIntegers K)
  · exact Finset.sum_congr rfl (fun Q _ => hterm Q)
  · rw [Ideal.sum_ramification_inertia_eq_finrank (R := NumberField.RingOfIntegers K)
      (S := NumberField.RingOfIntegers L) (p := P.asIdeal)]
    exact (IsFractionRing.finrank_eq (NumberField.RingOfIntegers K) K
      (NumberField.RingOfIntegers L) L).symm

end NK.ReconstructField
