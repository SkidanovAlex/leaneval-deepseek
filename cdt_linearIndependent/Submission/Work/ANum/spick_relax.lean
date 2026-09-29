import Mathlib
import Submission.Work.ANum.spick_shim

namespace Work.ANum

/-- Relaxed Schwarz–Pick estimate: if `f` is holomorphic on the unit disc and maps it into
itself, then for any `z` in the disc and any `a ≤ ‖f z‖`, `b ≥ ‖z‖` with `b < 1` we have
`‖f' z‖ ≤ (1 - a²)/(1 - b²)`.

This follows from `Commons.Analysis.Complex.schwarzPick_norm_deriv`
(`‖f' z‖ ≤ (1 - ‖f z‖²)/(1 - ‖z‖²)`) together with the monotonicity of the two sides:
`a² ≤ ‖f z‖²` and `1 - b² ≤ 1 - ‖z‖²`. -/
theorem spick_relax {f : ℂ → ℂ} {z : ℂ} {a b : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1))
    (hfm : Set.MapsTo f (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1))
    (ha0 : 0 ≤ a) (ha : a ≤ ‖f z‖) (hb : ‖z‖ ≤ b) (hb1 : b < 1) :
    ‖deriv f z‖ ≤ (1 - a ^ 2) / (1 - b ^ 2) := by
  have hb0 : 0 ≤ b := le_trans (norm_nonneg z) hb
  have hznorm : ‖z‖ < 1 := lt_of_le_of_lt hb hb1
  have hzmem : z ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_eq_norm]; simpa using hznorm
  have hfzmem : f z ∈ Metric.ball (0 : ℂ) 1 := hfm hzmem
  have hfznorm : ‖f z‖ < 1 := by
    rw [Metric.mem_ball, dist_eq_norm] at hfzmem; simpa using hfzmem
  have hclosed : Set.MapsTo f (Metric.ball (0 : ℂ) 1) (Metric.closedBall (0 : ℂ) 1) :=
    hfm.mono_right Metric.ball_subset_closedBall
  have hmain := Commons.Analysis.Complex.schwarzPick_norm_deriv hf hclosed hzmem hfznorm
  have hanum : 1 - ‖f z‖ ^ 2 ≤ 1 - a ^ 2 := by
    have h2 : a ^ 2 ≤ ‖f z‖ ^ 2 := by nlinarith [norm_nonneg (f z), ha, ha0]
    linarith
  have hden : 1 - b ^ 2 ≤ 1 - ‖z‖ ^ 2 := by
    have h2 : ‖z‖ ^ 2 ≤ b ^ 2 := by nlinarith [norm_nonneg z, hb, hb0]
    linarith
  have hdenpos1 : 0 < 1 - ‖z‖ ^ 2 := by nlinarith
  have hdenpos2 : 0 < 1 - b ^ 2 := by nlinarith
  have hnumpos : 0 ≤ 1 - a ^ 2 := by nlinarith
  calc ‖deriv f z‖ ≤ (1 - ‖f z‖ ^ 2) / (1 - ‖z‖ ^ 2) := hmain
    _ ≤ (1 - a ^ 2) / (1 - ‖z‖ ^ 2) :=
        div_le_div_of_nonneg_right hanum (le_of_lt hdenpos1)
    _ ≤ (1 - a ^ 2) / (1 - b ^ 2) :=
        div_le_div_of_nonneg_left hnumpos hdenpos2 hden

end Work.ANum
