import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.Order.CompletePartialOrder

namespace Commons.NumberTheory.NumberField.Set

theorem primeIdealZetaSum_union_of_disjoint {K : Type*} [Field K] [NumberField K]
    {S T : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
    (hST : Disjoint S T) (s : ℝ)
    (hS : Summable fun 𝔭 : S => (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s))
    (hT : Summable fun 𝔭 : T => (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :
    NumberField.Set.primeIdealZetaSum (S ∪ T) s =
      NumberField.Set.primeIdealZetaSum S s + NumberField.Set.primeIdealZetaSum T s := by
  rw [NumberField.Set.primeIdealZetaSum_def, NumberField.Set.primeIdealZetaSum_def,
    NumberField.Set.primeIdealZetaSum_def]
  exact Summable.tsum_union_disjoint
    (f := fun 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
      (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) hST hS hT

end Commons.NumberTheory.NumberField.Set