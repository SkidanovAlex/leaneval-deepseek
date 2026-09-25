import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.Order.CompletePartialOrder

open Filter IsDedekindDomain Topology Set
open scoped BigOperators

namespace Commons.NumberTheory.NumberField.Set

/-- Additivity of the partial Dirichlet series over a disjoint union of sets of primes,
assuming that the two partial sums converge. -/
theorem primeIdealZetaSum_union_of_disjoint {K : Type*} [Field K] [NumberField K]
    {S T : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
    (hST : Disjoint S T) (s : ℝ)
    (hS : Summable fun 𝔭 : S => (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s))
    (hT : Summable fun 𝔭 : T => (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)) :
    NumberField.Set.primeIdealZetaSum (S ∪ T) s =
      NumberField.Set.primeIdealZetaSum S s + NumberField.Set.primeIdealZetaSum T s := by
  have hS' : Summable (S.indicator
      (fun 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))) :=
    (summable_subtype_iff_indicator).mp hS
  have hT' : Summable (T.indicator
      (fun 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))) :=
    (summable_subtype_iff_indicator).mp hT
  rw [NumberField.Set.primeIdealZetaSum_def, NumberField.Set.primeIdealZetaSum_def,
    NumberField.Set.primeIdealZetaSum_def]
  rw [tsum_subtype (S ∪ T)
      (fun 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)),
    tsum_subtype S
      (fun 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)),
    tsum_subtype T
      (fun 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))]
  rw [Set.indicator_union_of_disjoint hST]
  exact Summable.tsum_add hS' hT'

/-- If `S` and `T` are disjoint sets of nonzero prime ideals with Dirichlet densities `δ₁`
and `δ₂`, then `S ∪ T` has Dirichlet density `δ₁ + δ₂`. -/
theorem hasDirichletDensity_union_of_disjoint {K : Type*} [Field K] [NumberField K]
    {S T : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
    (hST : Disjoint S T) {δ₁ δ₂ : ℝ}
    (hS : NumberField.Set.HasDirichletDensity S δ₁)
    (hT : NumberField.Set.HasDirichletDensity T δ₂) :
    NumberField.Set.HasDirichletDensity (S ∪ T) (δ₁ + δ₂) := by
  have key : ∀ s : ℝ,
      NumberField.Set.primeIdealZetaSum (S ∪ T) s /
          NumberField.Set.primeIdealZetaSum
            (univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s =
        NumberField.Set.primeIdealZetaSum S s /
            NumberField.Set.primeIdealZetaSum
              (univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s +
          NumberField.Set.primeIdealZetaSum T s /
            NumberField.Set.primeIdealZetaSum
              (univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s := by
    intro s
    by_cases hU : Summable
      (fun 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))
    · have hSs : Summable fun 𝔭 : S => (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) :=
        hU.subtype (· ∈ S)
      have hTs : Summable fun 𝔭 : T => (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) :=
        hU.subtype (· ∈ T)
      rw [primeIdealZetaSum_union_of_disjoint hST s hSs hTs, add_div]
    · have hU0 : NumberField.Set.primeIdealZetaSum
          (univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s = 0 := by
        rw [NumberField.Set.primeIdealZetaSum_def]
        rw [tsum_subtype (univ : Set (IsDedekindDomain.HeightOneSpectrum
              (NumberField.RingOfIntegers K)))
            (fun 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) =>
              (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))]
        rw [Set.indicator_univ]
        exact tsum_eq_zero_of_not_summable hU
      rw [hU0]
      simp
  exact (hS.add hT).congr' (Eventually.of_forall fun s => (key s).symm)

end Commons.NumberTheory.NumberField.Set