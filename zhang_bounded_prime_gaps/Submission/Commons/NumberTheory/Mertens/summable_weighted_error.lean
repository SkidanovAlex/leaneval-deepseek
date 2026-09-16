import Mathlib
import Submission.Commons.NumberTheory.Mertens.error_smoothSum_tendsto_zero

namespace Commons.NumberTheory.Mertens

theorem summable_weighted_error {e : ℕ → ℝ}
    (he : Filter.Tendsto e Filter.atTop (nhds 0)) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun k : ℕ => if 2 ≤ k then
      e k * (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0) := by
  exact (error_smoothSum_tendsto_zero he).1 hε

end Commons.NumberTheory.Mertens
