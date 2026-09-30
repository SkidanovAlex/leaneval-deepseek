import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.multiHom_assPrime
import Submission.Work.BW.map_scaleEnd_eq_self


namespace Work.BW.RB

/-- The minimal primes of a multihomogeneous ideal `I` of `MR N = ℂ[X_{i0}, X_{i1}]_i` are again
multihomogeneous.

Every minimal prime of `I` is the annihilator of a nonzero element of `MR N ⧸ I`, hence an
associated prime of `MR N ⧸ I` (Mathlib: minimal primes of the annihilator of a f.g. module are
associated primes). Since `I` is multihomogeneous, every torus scaling fixes `I` and therefore
permutes its associated primes; an associated prime fixed by all scalings is
multihomogeneous, which is `multiHom_assPrime`. -/
theorem multiHom_minimalPrimes {N : ℕ} (I : Ideal (MR N)) (hI : MultiHom N I) (q : Ideal (MR N))
    (hq : q ∈ I.minimalPrimes) : MultiHom N q := by
  have hann : Module.annihilator (MR N) ((MR N) ⧸ I) = I := Ideal.annihilator_quotient
  have hassoc : q ∈ associatedPrimes (MR N) ((MR N) ⧸ I) := by
    have h := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
      (MR N) ((MR N) ⧸ I)
    rw [hann] at h
    exact h hq
  exact multiHom_assPrime I hI q hassoc

end Work.BW.RB
