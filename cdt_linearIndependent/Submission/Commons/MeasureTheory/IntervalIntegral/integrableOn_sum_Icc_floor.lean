import Mathlib
import Submission.Commons.GeometryOfNumbers.Counting.sum_tailG_annulus_le_of_shell

namespace Commons.MeasureTheory.IntervalIntegral

open _root_.MeasureTheory

/-- The step function `t ↦ ∑_{h=1}^{⌊(t-1)/B⌋₊} c h` is integrable on any compact interval
`[1, v]`: it is measurable, and on `[1, v]` its index range is bounded by `⌊(v-1)/B⌋₊`, so it is
bounded there.  Integrability then follows from the bounded measurability criterion
(`Commons.GeometryOfNumbers.Counting.integrableOn_Icc_of_bound`). -/
theorem integrableOn_sum_Icc_floor (c : ℕ → ℝ) {B v : ℝ} (hB : 0 < B) :
    MeasureTheory.IntegrableOn (fun t : ℝ => ∑ h ∈ Finset.Icc 1 ⌊(t - 1) / B⌋₊, c h)
      (Set.Icc 1 v) := by
  refine Commons.GeometryOfNumbers.Counting.integrableOn_Icc_of_bound
    (C := ∑ h ∈ Finset.Icc 1 ⌊(v - 1) / B⌋₊, |c h|) ?_ ?_
  · measurability
  · intro x hx
    rw [Set.mem_Icc] at hx
    obtain ⟨hx1, hxv⟩ := hx
    refine le_trans (Finset.abs_sum_le_sum_abs c (Finset.Icc 1 ⌊(x - 1) / B⌋₊)) ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · apply Finset.Icc_subset_Icc_right
      apply Nat.floor_le_floor
      apply div_le_div_of_nonneg_right _ hB.le
      linarith
    · intro h _ _
      exact abs_nonneg _

end Commons.MeasureTheory.IntervalIntegral
