import Mathlib
import Submission.Work.Mostow.BdExt.Basic

namespace Work.Mostow.BdExt

open Submission.Mostow

/-- A sequence in the chart space `E n` whose successive differences are dominated by the terms of a
summable nonnegative real series is convergent: it is the sequence of partial sums of the series of
increments `x (k+1) - x k`, which is absolutely convergent, hence convergent in the complete space
`E n`. -/
theorem stepSum (n : ℕ) (x : ℕ → Submission.Mostow.E n) (b : ℕ → ℝ)
    (hb : ∀ k, 0 ≤ b k) (hsum : Summable b) (hstep : ∀ k, ‖x (k + 1) - x k‖ ≤ b k) :
    ∃ η, Filter.Tendsto x Filter.atTop (nhds η) := by
  -- the increments and their absolute convergence
  set y : ℕ → Submission.Mostow.E n := fun k => x (k + 1) - x k with hy_def
  have hnorm : Summable (fun k => ‖y k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hstep hsum
  have hy : Summable y := Summable.of_norm hnorm
  -- `x` is the sequence of partial sums of `y`, shifted by `x 0`
  refine ⟨x 0 + ∑' k, y k, ?_⟩
  have hx : ∀ m, x 0 + ∑ k ∈ Finset.range m, y k = x m := by
    intro m
    simp only [hy_def]
    rw [Finset.sum_range_sub]
    abel
  refine (hy.hasSum.tendsto_sum_nat.const_add (x 0)).congr' ?_
  filter_upwards with m
  exact hx m

end Work.Mostow.BdExt
