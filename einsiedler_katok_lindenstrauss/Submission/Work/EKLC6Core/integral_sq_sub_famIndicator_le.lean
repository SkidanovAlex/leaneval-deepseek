import Mathlib
import Submission.Work.EKLC6Core.famIndicatorSum
import Submission.Work.EKLC6Core.famIndicator

/-!
# `Work.EKLC6Core.integral_sq_sub_famIndicator_le`

An `L²` bound for the difference between a real finite combination of indicators of the family
`S : ℕ → Set X` and the `famIndicator` of a rational combination `q` supported in the same finite
index set `ι`:

`∫ ((∑ n ∈ ι, c n * 1_{S n}) - famIndicator S q)² ∂ν ≤ (∑ n ∈ ι, |c n - q n|)²`

for every probability measure `ν`.  The pointwise input is
`Work.EKLC6Core.abs_sub_famIndicator_le`; since every indicator takes values in `{0,1}`, the
difference is pointwise dominated by the `ℓ¹`-norm of the coefficient error, and integrating the
square against a probability measure costs nothing.
-/

open MeasureTheory MeasureTheory.Measure

namespace Work.EKLC6Core

theorem integral_sq_sub_famIndicator_le {X : Type*} [MeasurableSpace X] (S : ℕ → Set X)
    (hS : ∀ n, MeasurableSet (S n)) (ν : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure ν] (ι : Finset ℕ) (c : ℕ → ℝ) (q : ℕ →₀ ℚ)
    (hq : q.support ⊆ ι) :
    ∫ x, ((∑ n ∈ ι, c n * (S n).indicator (fun _ => (1 : ℝ)) x)
        - Work.EKLC6Core.famIndicator S q x) ^ 2 ∂ν
      ≤ (∑ n ∈ ι, |c n - (q n : ℝ)|) ^ 2 := by
  set R : ℝ := ∑ n ∈ ι, |c n - (q n : ℝ)| with hR
  -- Pointwise domination of the squared difference by `R ^ 2`.
  have hpoint : ∀ x, ((∑ n ∈ ι, c n * (S n).indicator (fun _ => (1 : ℝ)) x)
      - Work.EKLC6Core.famIndicator S q x) ^ 2 ≤ R ^ 2 := by
    intro x
    have hle := Work.EKLC6Core.abs_sub_famIndicator_le S ι c q hq x
    rw [← hR] at hle
    have hRnn : 0 ≤ R := by
      rw [hR]; exact Finset.sum_nonneg fun n _ => abs_nonneg _
    obtain ⟨h1, h2⟩ := abs_le.mp hle
    nlinarith [sq_nonneg ((∑ n ∈ ι, c n * (S n).indicator (fun _ => (1 : ℝ)) x)
      - Work.EKLC6Core.famIndicator S q x)]
  -- Measurability of the squared difference.
  have hmeas : AEStronglyMeasurable (fun x => ((∑ n ∈ ι,
      c n * (S n).indicator (fun _ => (1 : ℝ)) x)
        - Work.EKLC6Core.famIndicator S q x) ^ 2) ν := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.pow_const
    apply Measurable.sub
    · exact Finset.measurable_sum _
        fun n _ => measurable_const.mul (Measurable.indicator measurable_const (hS n))
    · exact Work.EKLC6Core.measurable_famIndicator S hS q
  -- Integrability of the squared difference (bounded by `R ^ 2`).
  have hint : Integrable (fun x => ((∑ n ∈ ι, c n * (S n).indicator (fun _ => (1 : ℝ)) x)
      - Work.EKLC6Core.famIndicator S q x) ^ 2) ν :=
    Integrable.of_bound hmeas (R ^ 2) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpoint x)
  calc ∫ x, ((∑ n ∈ ι, c n * (S n).indicator (fun _ => (1 : ℝ)) x)
        - Work.EKLC6Core.famIndicator S q x) ^ 2 ∂ν
      ≤ ∫ x, R ^ 2 ∂ν := integral_mono hint (integrable_const _) hpoint
    _ = R ^ 2 := by
        rw [integral_const, hR]
        simp [Measure.real, IsProbabilityMeasure.measure_univ]

end Work.EKLC6Core
