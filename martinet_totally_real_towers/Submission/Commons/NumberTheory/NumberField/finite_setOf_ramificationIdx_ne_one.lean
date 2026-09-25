import Mathlib
import Submission.Commons.NumberTheory.NumberField.differentIdeal_eq_top_of_ramificationIdx

namespace Commons.NumberTheory.NumberField

open scoped Classical

/-- In a finite extension of number fields `K ⊆ L`, only finitely many nonzero prime ideals of
`𝓞 L` ramify over `𝓞 K`.

The ramified primes are exactly the prime divisors of the relative different
`differentIdeal (𝓞 K) (𝓞 L)` (a nonzero ideal, by `differentIdeal_ne_bot`), and a nonzero ideal
in a Dedekind domain has only finitely many prime divisors. -/
theorem finite_setOf_ramificationIdx_ne_one {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] : {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) | q.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) ≠ 1}.Finite := by
  let D := differentIdeal (NumberField.RingOfIntegers K) (NumberField.RingOfIntegers L)
  have hD : D ≠ ⊥ := differentIdeal_ne_bot
  have hinj : Function.Injective
      (fun q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) => q.asIdeal) :=
    fun a b h => by
      have h' : a.asIdeal = b.asIdeal := h
      ext x; rw [h']
  -- The ramified primes are among the (finitely many) prime divisors of the different `D`.
  have hfin : ((fun q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L) =>
      q.asIdeal) ⁻¹'
      ((UniqueFactorizationMonoid.normalizedFactors D).toFinset :
        Set (Ideal (NumberField.RingOfIntegers L)))).Finite :=
    Set.Finite.preimage (fun _ _ _ _ h => hinj h) (Finset.finite_toSet _)
  refine Set.Finite.subset hfin ?_
  intro q hq
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
  refine (Ideal.mem_normalizedFactors_iff hD).mpr ⟨q.isPrime, ?_⟩
  have hdiv : q.asIdeal ∣ D := by
    by_contra h
    exact hq ((ramificationIdx_one_iff_not_dvd_differentIdeal q.asIdeal q.isPrime).mp h)
  exact Ideal.dvd_iff_le.mp hdiv

end Commons.NumberTheory.NumberField
