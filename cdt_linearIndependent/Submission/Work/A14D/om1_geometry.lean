import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.H_cont

namespace Work.A14D

open Work.A14D

/-!
# `Work.A14D.om1_geometry`

Elementary geometry of the two half-planes
`SU = {z | (1 − Re z)/8 < Im z}`, `SL = {z | Im z < (Re z − 1)/8}`
and the slit plane `Om1 = {z | Im z ≠ 0 ∨ 1 < Re z}`, together with the non-vanishing of
`PZ z = z(1−z)(1−9z)` there.

The half-plane facts (`convex_SU`, `isOpen_SU_H_cont`, `convex_SL`, `isOpen_SL_H_cont`,
`PZ_ne_zero_of_mem_SU`, `PZ_ne_zero_of_mem_SL`, and the normal forms `mem_SU_iff`, `mem_SL_iff`)
are already proved in `Submission.Work.A14D.H_cont`; here we add the containment in `Om1`, the
trichotomy for `Om1`, and the non-vanishing on the two open half-planes `Im ≠ 0`, which all follow
from the fact that the three roots `0, 1, 1/9` of `PZ` are real.
-/

/-- The only zeros of `PZ z = z(1−z)(1−9z)` are `0`, `1` and `1/9`; in particular at any zero
`z.im = 0`. -/
lemma PZ_im_eq_zero_of_eq_zero {z : ℂ} (h : PZ z = 0) : z.im = 0 := by
  rw [PZ] at h
  rcases mul_eq_zero.mp h with h2 | h2
  · rcases mul_eq_zero.mp h2 with h2 | h2
    · rw [h2]; simp
    · have hz : z = 1 := by linear_combination -h2
      rw [hz]; simp
  · have h3 : 9 * z = 1 := by linear_combination -h2
    have hz : z = 1 / 9 := by
      rw [eq_div_iff (by norm_num : (9 : ℂ) ≠ 0)]
      linear_combination h3
    rw [hz]; norm_num

lemma PZ_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) : PZ z ≠ 0 := by
  intro h
  rw [PZ_im_eq_zero_of_eq_zero h] at hz
  exact lt_irrefl _ hz

lemma PZ_ne_zero_of_im_neg {z : ℂ} (hz : z.im < 0) : PZ z ≠ 0 := by
  intro h
  rw [PZ_im_eq_zero_of_eq_zero h] at hz
  exact lt_irrefl _ hz

lemma SU_subset_Om1 : SU ⊆ Om1 := by
  intro z hz
  rw [mem_SU_iff] at hz
  by_cases him : z.im = 0
  · right; rw [him] at hz; linarith
  · left; exact him

lemma SL_subset_Om1 : SL ⊆ Om1 := by
  intro z hz
  rw [mem_SL_iff] at hz
  by_cases him : z.im = 0
  · right; rw [him] at hz; linarith
  · left; exact him

lemma Om1_trichotomy : ∀ z : ℂ, z ∈ Om1 → 0 < z.im ∨ z.im < 0 ∨ z ∈ SU ∩ SL := by
  intro z hz
  rcases hz with him | hre
  · rcases lt_or_gt_of_ne him with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  · by_cases him : z.im = 0
    · refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · rw [mem_SU_iff, him]; linarith
      · rw [mem_SL_iff, him]; linarith
    · rcases lt_or_gt_of_ne him with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h

theorem om1_geometry :
    Convex ℝ SU ∧ IsOpen SU ∧ SU ⊆ Om1 ∧
    Convex ℝ SL ∧ IsOpen SL ∧ SL ⊆ Om1 ∧
    (∀ z : ℂ, z ∈ Om1 → 0 < z.im ∨ z.im < 0 ∨ z ∈ SU ∩ SL) ∧
    (∀ z : ℂ, 0 < z.im → PZ z ≠ 0) ∧
    (∀ z : ℂ, z.im < 0 → PZ z ≠ 0) ∧
    (∀ z : ℂ, z ∈ SU → PZ z ≠ 0) ∧
    (∀ z : ℂ, z ∈ SL → PZ z ≠ 0) := by
  refine ⟨convex_SU, isOpen_SU_H_cont, SU_subset_Om1,
    convex_SL, isOpen_SL_H_cont, SL_subset_Om1,
    Om1_trichotomy, ?_, ?_, ?_, ?_⟩
  · intro z hz; exact PZ_ne_zero_of_im_pos hz
  · intro z hz; exact PZ_ne_zero_of_im_neg hz
  · intro z hz; exact PZ_ne_zero_of_mem_SU hz
  · intro z hz; exact PZ_ne_zero_of_mem_SL hz

end Work.A14D
