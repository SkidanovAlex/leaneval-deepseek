import Mathlib
import Submission.Work.PL.Approx.Defs

namespace Work.PL.Approx.Cutoff

/-- The one-dimensional cutoff vanishes as soon as `b ≤ |u|`. -/
lemma seg_eq_zero_of_le_abs {a b u : ℝ} (hab : a < b) (hu : b ≤ |u|) : seg a b u = 0 := by
  have hba : 0 < b - a := by linarith
  have ht : (b - |u|) / (b - a) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith
    · linarith
  unfold seg clamp
  rw [min_eq_right (by linarith : (b - |u|) / (b - a) ≤ 1)]
  exact max_eq_left ht

lemma cubeCut_eq_zero {n : ℕ} {a b : ℝ} (hab : a < b) {x : PL.E n} (hx : ∃ i, b ≤ |x i|) : cubeCut a b x = 0 := by
  obtain ⟨i, hi⟩ := hx
  unfold cubeCut
  exact Finset.prod_eq_zero (Finset.mem_univ i) (seg_eq_zero_of_le_abs hab hi)

end Work.PL.Approx.Cutoff
