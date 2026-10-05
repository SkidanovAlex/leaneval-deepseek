import Mathlib
import Submission.Work.RPCore.Defs
import Submission.Work.RPCore.Flow.smooth_cutoff
import Submission.Work.RPCore.Flow.antideriv_contDiff
import Submission.Work.RPCore.Flow.antideriv_eq_self
import Submission.Work.RPCore.Flow.antideriv_bdd

namespace Work.RPCore.Flow

open MeasureTheory intervalIntegral

/-- A `C^4` (indeed `C^∞`) "clamp": the identity on `[-1,2]`, smoothly flattened outside
to a bounded function with bounded derivative.  Concretely we take an antiderivative of a
smooth cutoff function which is `1` on `[-1,2]` and `0` outside `[-2,3]`. -/
theorem exists_clamp : ∃ ψ : ℝ → ℝ, ContDiff ℝ 4 ψ ∧ (∀ t ∈ Set.Icc (-1 : ℝ) 2, ψ t = t) ∧
    (∃ B : ℝ, ∀ t, |ψ t| ≤ B) ∧ (∃ B' : ℝ, ∀ t, |deriv ψ t| ≤ B') := by
  obtain ⟨c, hc_smooth, hc_one, hc_bounds, hc_left, hc_right⟩ := smooth_cutoff
  have hc_cont : Continuous c := hc_smooth.continuous
  refine ⟨fun t => ∫ s in (0 : ℝ)..t, c s, ?_, ?_, ?_, ?_⟩
  · exact (antideriv_contDiff c hc_smooth).of_le (by norm_num)
  · exact antideriv_eq_self c hc_one
  · obtain ⟨B, hB⟩ := antideriv_bdd c hc_cont (fun t => (hc_bounds t).1)
      (fun t => (hc_bounds t).2) hc_left hc_right
    exact ⟨B, hB⟩
  · refine ⟨1, fun t => ?_⟩
    rw [Continuous.deriv_integral c hc_cont 0 t]
    exact abs_le.mpr ⟨by linarith [(hc_bounds t).1], (hc_bounds t).2⟩

end Work.RPCore.Flow
