import Mathlib
import Submission.Commons.NumberTheory.NumberField.Set.hasDirichletDensity_union_of_disjoint
import Submission.Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum

open Filter IsDedekindDomain Topology Set
open scoped BigOperators

namespace Commons.NumberTheory.NumberField.Set

/-- Comparison of the sums of a nonnegative summable real series over two sets, the first
contained in the second. -/
theorem tsum_subtype_le_tsum_subtype_of_subset {ι : Type*} {f : ι → ℝ} (hsum : Summable f)
    {A B : Set ι} (hAB : A ⊆ B) (hf : ∀ i, 0 ≤ f i) :
    (∑' i : A, f i) ≤ ∑' i : B, f i := by
  have hA : Summable fun i : A => f i := hsum.subtype A
  have hB : Summable fun i : B => f i := hsum.subtype B
  have hAi : Summable (A.indicator f) := (summable_subtype_iff_indicator).mp hA
  have hBi : Summable (B.indicator f) := (summable_subtype_iff_indicator).mp hB
  rw [tsum_subtype A f, tsum_subtype B f]
  exact Summable.tsum_le_tsum (fun i => by
    by_cases hi : i ∈ A
    · rw [indicator_of_mem hi, indicator_of_mem (hAB hi)]
    · rw [indicator_of_notMem hi]
      exact indicator_nonneg (fun j _ => hf j) i) hAi hBi

/-- The prime ideal zeta sum of a number field is monotone in the set of prime ideals, at least
for `s > 1`, where the series converges. -/
theorem primeIdealZetaSum_mono {K : Type*} [Field K] [NumberField K]
    {S T : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} (hST : S ⊆ T)
    {s : ℝ} (hs : 1 < s) :
    NumberField.Set.primeIdealZetaSum S s ≤ NumberField.Set.primeIdealZetaSum T s := by
  rw [NumberField.Set.primeIdealZetaSum_def, NumberField.Set.primeIdealZetaSum_def]
  exact tsum_subtype_le_tsum_subtype_of_subset (summable_primeIdealZetaSum hs) hST
    (fun 𝔭 => by positivity)

/-- A set of prime ideals contained in a set of Dirichlet density `0` has Dirichlet density `0`. -/
theorem hasDirichletDensity_zero_of_subset {K : Type*} [Field K] [NumberField K]
    {S T : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))}
    (hT : NumberField.Set.HasDirichletDensity T 0) (hST : S ⊆ T) :
    NumberField.Set.HasDirichletDensity S 0 := by
  unfold NumberField.Set.HasDirichletDensity at hT ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT ?_ ?_
  · filter_upwards with s
    exact div_nonneg (NumberField.Set.primeIdealZetaSum_nonneg S s)
      (NumberField.Set.primeIdealZetaSum_nonneg
        (univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact div_le_div_of_nonneg_right (primeIdealZetaSum_mono hST hs)
      (NumberField.Set.primeIdealZetaSum_nonneg
        (univ : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) s)

theorem hasDirichletDensity_union_of_density_zero {K : Type*} [Field K] [NumberField K]
    {S T : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))} {δ : ℝ}
    (hS : NumberField.Set.HasDirichletDensity S δ)
    (hT : NumberField.Set.HasDirichletDensity T 0) :
    NumberField.Set.HasDirichletDensity (S ∪ T) δ := by
  have hTS : NumberField.Set.HasDirichletDensity (T \ S) 0 :=
    hasDirichletDensity_zero_of_subset hT sdiff_subset
  have h₂ := hasDirichletDensity_union_of_disjoint (S := S) (T := T \ S)
    disjoint_sdiff_self_right hS hTS
  rwa [union_sdiff_self, add_zero] at h₂

end Commons.NumberTheory.NumberField.Set
