import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Commons.MeasureTheory.Measure

open _root_.MeasureTheory Filter
open scoped Topology

/-- A coordinate hyperplane is Lebesgue-null in `ℝ^k`. -/
theorem volume_coord_eq_zero {k : ℕ} (j : Fin k) (c : ℝ) :
    (volume : _root_.MeasureTheory.Measure (Fin k → ℝ)) {t | t j = c} = 0 := by
  rw [volume_pi]
  exact Measure.pi_eval_preimage_null (fun _ => (volume : Measure ℝ)) Real.volume_singleton

end Commons.MeasureTheory.Measure