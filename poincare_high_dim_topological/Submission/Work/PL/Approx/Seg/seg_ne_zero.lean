import Mathlib
import Submission.Work.PL.Approx.Defs

namespace Work.PL.Approx.Seg

/-- If the one-dimensional cutoff `seg a b u` is nonzero (with `a < b`), then `u` lies strictly
inside the ball of radius `b`. -/
lemma seg_ne_zero {a b u : ℝ} (hab : a < b) (h : seg a b u ≠ 0) : |u| < b := by
  have hba : 0 < b - a := by linarith
  have h1 : 0 < (b - |u|) / (b - a) := by
    by_contra hle
    have hle' : (b - |u|) / (b - a) ≤ 0 := not_lt.mp hle
    apply h
    unfold seg clamp
    rw [min_eq_right (by linarith), max_eq_left hle']
  have hb : 0 < b - |u| := by
    rcases (div_pos_iff.mp h1) with ⟨hx, _⟩ | ⟨hx, _⟩
    · exact hx
    · linarith
  linarith

end Work.PL.Approx.Seg
