import Mathlib

namespace Work.EKLComp

/-- If a monotone increasing sequence of (not necessarily measurable) sets all have
`μ`-measure at most `c` in the real-valued sense, then so does their union, provided `μ`
is a finite measure.  This is continuity of a measure from below together with the fact
that a finite measure is never `∞` on a set. -/
theorem hopf_measure_iUnion_step {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsFiniteMeasure μ] {A : ℕ → Set X} (hmono : Monotone A) {c : ℝ}
    (h : ∀ n : ℕ, (μ (A n)).toReal ≤ c) :
    μ (⋃ n, A n) ≤ ENNReal.ofReal c := by
  -- Continuity from below: the measure of the union is the supremum of the measures.
  rw [hmono.measure_iUnion]
  refine iSup_le fun n => ?_
  -- For a finite measure, `μ (A n) ≠ ∞`, so `ofReal (μ (A n)).toReal = μ (A n)`.
  rw [← ENNReal.ofReal_toReal (MeasureTheory.measure_ne_top μ (A n))]
  exact ENNReal.ofReal_le_ofReal (h n)

end Work.EKLComp
