import Mathlib

namespace Work.HornCov

/-- A countable subset of `ℂ` cannot contain a whole ball of positive radius:
the (open) ball has positive Lebesgue measure while a countable set is null. -/
theorem exists_mem_ball_notMem_of_countable {C : Set ℂ} (hC : C.Countable) {c : ℂ} {r : ℝ} (hr : 0 < r) :
    ∃ w ∈ Metric.ball c r, w ∉ C := by
  by_contra h
  have hsub : Metric.ball c r ⊆ C := by
    intro z hz
    by_contra hzC
    exact h ⟨z, hz, hzC⟩
  have h0 : (MeasureTheory.volume : MeasureTheory.Measure ℂ) C = 0 :=
    hC.measure_zero MeasureTheory.volume
  have hpos : 0 < (MeasureTheory.volume : MeasureTheory.Measure ℂ) (Metric.ball c r) :=
    Metric.measure_ball_pos MeasureTheory.volume c hr
  have hle : (MeasureTheory.volume : MeasureTheory.Measure ℂ) (Metric.ball c r)
      ≤ (MeasureTheory.volume : MeasureTheory.Measure ℂ) C :=
    MeasureTheory.measure_mono hsub
  rw [h0] at hle
  exact (not_lt_of_ge hle) hpos

end Work.HornCov
