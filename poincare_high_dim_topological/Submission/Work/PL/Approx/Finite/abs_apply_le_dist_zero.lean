import Mathlib
import Submission.Work.PL.Approx.Defs

namespace Work.PL.Approx.Finite

lemma abs_apply_le_dist_zero {n : ℕ} (v : PL.E n) : ∀ i : Fin n, |v i| ≤ dist v 0 := by
  intro i
  rw [dist_eq_norm, sub_zero]
  have h : ‖v i‖ ≤ ‖v‖ := PiLp.norm_apply_le v i
  rwa [Real.norm_eq_abs] at h

end Work.PL.Approx.Finite
