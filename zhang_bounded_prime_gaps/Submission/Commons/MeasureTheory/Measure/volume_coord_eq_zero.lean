import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Commons.MeasureTheory.Integral.tendsto_integral_sq_of_dominated

namespace Commons.MeasureTheory.Measure

open _root_.MeasureTheory Filter
open scoped Topology

/-- A coordinate hyperplane is Lebesgue-null in `ℝ^k`. -/
theorem volume_coord_eq_zero {k : ℕ} (j : Fin k) (c : ℝ) :
    (volume : _root_.MeasureTheory.Measure (Fin k → ℝ)) {t | t j = c} = 0 := by
  rw [volume_pi]
  exact Measure.pi_eval_preimage_null (fun _ => (volume : Measure ℝ)) Real.volume_singleton

end Commons.MeasureTheory.Measure