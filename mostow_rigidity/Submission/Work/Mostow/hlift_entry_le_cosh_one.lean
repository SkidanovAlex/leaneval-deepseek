import Mathlib
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.poAux

namespace Work.Mostow

open Submission.Mostow

/-- Every entry of the hyperboloid lift `hlift v` of a chart point `v` inside the unit ball around
the base point `0` is bounded by `cosh 1`.  The time entry is `tpart v = cosh (hdist 0 v)`, and the
space entries are bounded by `‖v‖ = sinh (hdist 0 v) ≤ sinh 1 < cosh 1`. -/
theorem hlift_entry_le_cosh_one {n : ℕ} {v : Submission.Mostow.E n}
    (hv : Submission.Mostow.hdist (0 : Submission.Mostow.E n) v ≤ 1) :
    ∀ k : Fin n ⊕ Fin 1, |Submission.Mostow.hlift v k| ≤ Real.cosh 1 := by
  have h0 : 0 ≤ hdist (0 : E n) v := hdist_nonneg _ _
  have hcosh : tpart v ≤ Real.cosh 1 := by
    have h := (Real.cosh_le_cosh (x := hdist (0 : E n) v) (y := 1)).2 (by
      rw [abs_of_nonneg h0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]; exact hv)
    rwa [cosh_hdist_zero] at h
  have hnorm : ‖v‖ ≤ Real.cosh 1 := by
    rw [← sinh_hdist_zero v]
    exact le_trans (Real.sinh_le_sinh.2 hv) (le_of_lt (Real.sinh_lt_cosh 1))
  intro k
  rcases k with i | j
  · rw [hlift_inl]
    exact le_trans (by simpa using PiLp.norm_apply_le v i) hnorm
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [hlift_inr, abs_of_nonneg (le_of_lt (tpart_pos v))]
    exact hcosh

end Work.Mostow
