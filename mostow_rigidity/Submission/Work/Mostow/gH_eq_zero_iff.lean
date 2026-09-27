import Mathlib
import Submission.Work.Mostow.localIsomDefs

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

theorem gH_eq_zero_iff {n : ℕ} (u v : E n) : gH u v = 0 ↔ v = 0 := by
  constructor
  · intro h
    rw [gH] at h
    have hmul : ‖v‖ ^ 2 * (1 + ‖u‖ ^ 2) = (inner ℝ u v) ^ 2 := by
      field_simp at h
      linarith
    have hcs : (inner ℝ u v) ^ 2 ≤ ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
      have := real_inner_mul_inner_self_le u v
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at this
      simpa [pow_two] using this
    have hv2 : ‖v‖ ^ 2 = 0 := le_antisymm (by nlinarith [hcs, hmul]) (by positivity)
    have hv : ‖v‖ = 0 := sq_eq_zero_iff.mp hv2
    exact norm_eq_zero.mp hv
  · intro h
    subst h
    simp [gH]

end Work.Mostow
