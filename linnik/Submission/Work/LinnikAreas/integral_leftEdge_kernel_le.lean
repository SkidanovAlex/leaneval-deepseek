import Mathlib
import Submission.Work.LinnikAreas.tentLeftEdgeDeps
import Submission.Commons.Analysis.Integral.integral_log_weight_le

namespace Work.LinnikAreas

open MeasureTheory

/-- The left-edge tent kernel `t ↦ (1 + log (|t| + 2)) / (9/4 + t²)` is pointwise
dominated by `t ↦ (log (2 + |t|) + 1) / (1 + t²)`, whose integral is ≤ 40. -/
theorem integral_leftEdge_kernel_le :
    (∫ t : ℝ, (1 + Real.log (|t| + 2)) / (9 / 4 + t ^ 2)) ≤ 80 := by
  have hg_int : Integrable (fun t : ℝ => (Real.log (2 + |t|) + 1) / (1 + t ^ 2)) := by
    have h := Commons.Analysis.Integral.integrable_log_lorentz 1 0 (by norm_num)
    simpa using h
  have hf_nonneg : 0 ≤ᵐ[volume]
      (fun t : ℝ => (1 + Real.log (|t| + 2)) / (9 / 4 + t ^ 2)) := by
    filter_upwards with t
    apply div_nonneg
    · have h1 : (1:ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
      have : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg h1
      linarith
    · positivity
  have hle : (fun t : ℝ => (1 + Real.log (|t| + 2)) / (9 / 4 + t ^ 2))
      ≤ᵐ[volume] (fun t : ℝ => (Real.log (2 + |t|) + 1) / (1 + t ^ 2)) := by
    filter_upwards with t
    have h1 : (1:ℝ) ≤ 2 + |t| := by linarith [abs_nonneg t]
    have hN : 0 ≤ Real.log (2 + |t|) + 1 := by
      have : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg h1
      linarith
    have hden : (0:ℝ) < 1 + t ^ 2 := by positivity
    have hden2 : (1:ℝ) + t ^ 2 ≤ 9 / 4 + t ^ 2 := by norm_num
    have h := div_le_div_of_nonneg_left hN hden hden2
    simpa [add_comm] using h
  have h1 : (∫ t : ℝ, (1 + Real.log (|t| + 2)) / (9 / 4 + t ^ 2))
      ≤ ∫ t : ℝ, (Real.log (2 + |t|) + 1) / (1 + t ^ 2) :=
    integral_mono_of_nonneg hf_nonneg hg_int hle
  have h2 : (∫ t : ℝ, (Real.log (2 + |t|) + 1) / (1 + t ^ 2)) ≤ 40 :=
    Commons.Analysis.Integral.integral_log_weight_le
  linarith

end Work.LinnikAreas
