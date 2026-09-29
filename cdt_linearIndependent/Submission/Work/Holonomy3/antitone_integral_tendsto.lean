import Mathlib

namespace Work.Holonomy3

/-- Dominated convergence for a decreasing (antitone) sequence of integrable functions
that is pointwise bounded below by an integrable function and converges pointwise to it.
The dominating function is `|f| + |u 0|`: since `f ≤ u n ≤ u 0` pointwise, each `u n`
is trapped between `f` and `u 0`, hence bounded in absolute value by `|f| + |u 0|`. -/
theorem antitone_integral_tendsto {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsFiniteMeasure μ] {f : X → ℝ} (hf : MeasureTheory.Integrable f μ)
    {u : ℕ → X → ℝ} (hu : ∀ n, MeasureTheory.Integrable (u n) μ)
    (huf : ∀ n x, f x ≤ u n x)
    (hmono : ∀ x, Antitone (fun n => u n x))
    (htend : ∀ x, Filter.Tendsto (fun n => u n x) Filter.atTop (nhds (f x))) :
    Filter.Tendsto (fun n => ∫ x, u n x ∂μ) Filter.atTop (nhds (∫ x, f x ∂μ)) := by
  refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun a => |f a| + |u 0 a|)
    (fun n => (hu n).aestronglyMeasurable) ?_ ?_ ?_
  · exact hf.abs.add (hu 0).abs
  · intro n
    filter_upwards with a
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have h1 : -( |f a|) ≤ f a := neg_abs_le (f a)
      have h2 : |f a| ≤ |f a| + |u 0 a| := le_add_of_nonneg_right (abs_nonneg _)
      linarith [huf n a]
    · have h1 : u 0 a ≤ |u 0 a| := le_abs_self _
      have h2 : |u 0 a| ≤ |f a| + |u 0 a| := le_add_of_nonneg_left (abs_nonneg _)
      have h3 : u n a ≤ u 0 a := hmono a (Nat.zero_le n)
      linarith
  · filter_upwards with a
    exact htend a

end Work.Holonomy3
