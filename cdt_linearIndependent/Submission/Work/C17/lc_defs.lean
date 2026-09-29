
import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17.logPw_setup

/-!
# Area C17 — numerical facts for `Work.C17.relation_to_LC`
-/

namespace Work.C17

open scoped BigOperators Topology

noncomputable section

lemma normSq_p0C : Complex.normSq p0C = (41 : ℝ) / 400 := by
  rw [Complex.normSq_apply]
  simp [p0C]
  norm_num

lemma norm_p0C_sq : ‖p0C‖ ^ 2 = (41 : ℝ) / 400 := by
  rw [Complex.sq_norm, normSq_p0C]

lemma norm_p0C_le : ‖p0C‖ ≤ (33 : ℝ) / 100 := by
  have h := norm_p0C_sq
  nlinarith [norm_nonneg p0C]

lemma normSq_p0C_sub_one : Complex.normSq (p0C - 1) = (241 : ℝ) / 400 := by
  rw [Complex.normSq_apply]
  simp [p0C]
  norm_num

lemma norm_p0C_sub_one_sq : ‖p0C - 1‖ ^ 2 = (241 : ℝ) / 400 := by
  rw [Complex.sq_norm, normSq_p0C_sub_one]

lemma norm_p0C_sub_one_pos : 0 < ‖p0C - 1‖ := by
  rcases eq_or_lt_of_le (norm_nonneg (p0C - 1)) with h0 | h0
  · have h := norm_p0C_sub_one_sq
    rw [← h0] at h
    norm_num at h
  · exact h0

lemma norm_p0C_div_le : ‖p0C / (p0C - 1)‖ ≤ (1 : ℝ) / 2 := by
  rw [norm_div, div_le_iff₀ (norm_p0C_sub_one_pos)]
  have h1 : ‖p0C - 1‖ ^ 2 = (241 : ℝ) / 400 := norm_p0C_sub_one_sq
  have h2 : ‖p0C‖ ^ 2 = (41 : ℝ) / 400 := norm_p0C_sq
  nlinarith [norm_nonneg p0C, norm_nonneg (p0C - 1),
    sq_nonneg (2 * ‖p0C‖ - ‖p0C - 1‖), sq_nonneg (2 * ‖p0C‖ + ‖p0C - 1‖)]

end

end Work.C17
