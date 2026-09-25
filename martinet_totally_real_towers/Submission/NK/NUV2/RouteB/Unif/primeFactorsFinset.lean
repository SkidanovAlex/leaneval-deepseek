import Mathlib
import Submission.NK.HeckeL.Basic

namespace NK.NUV2.RouteB.Unif

theorem primeFactorsFinset (K : Type) [Field K] [NumberField K]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ 0) :
    ∃ T : Finset (NK.HeckeL.PrimeIdeal K),
      ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, 𝔭 ∈ T ↔ 𝔭.asIdeal ∣ 𝔪 := by
  refine ⟨(Ideal.finite_factors (R := NumberField.RingOfIntegers K) h𝔪).toFinset, fun 𝔭 => ?_⟩
  exact (Ideal.finite_factors (R := NumberField.RingOfIntegers K) h𝔪).mem_toFinset

end NK.NUV2.RouteB.Unif
