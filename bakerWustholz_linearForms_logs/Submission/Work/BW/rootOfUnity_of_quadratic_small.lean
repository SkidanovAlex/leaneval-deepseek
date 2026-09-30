import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- If `α : ℂ` is a root of `X ^ 2 + t * X + s` with `s = ±1` and `(t, s)` among
the small pairs `(t, 1)` with `-2 ≤ t ≤ 2`, or `(0, -1)`, then `α` is a root of unity.
Concretely the possible roots are `±1`, `±i`, and the primitive third/sixth roots
of unity, all of which satisfy `α ^ 12 = 1`. -/
theorem rootOfUnity_of_quadratic_small (α : ℂ) (t s : ℤ)
    (hsmall : (s = 1 ∧ -2 ≤ t ∧ t ≤ 2) ∨ (s = -1 ∧ t = 0))
    (h : α ^ 2 + (t : ℂ) * α + (s : ℂ) = 0) :
    ∃ k : ℕ, 0 < k ∧ α ^ k = 1 := by
  rcases hsmall with ⟨hs, ht1, ht2⟩ | ⟨hs, ht⟩
  · -- s = 1, -2 ≤ t ≤ 2
    rw [hs] at h
    have ht : t = -2 ∨ t = -1 ∨ t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases ht with h2 | h2 | h2 | h2 | h2
    · -- t = -2: (α - 1) ^ 2 = 0, so α = 1
      rw [h2] at h; push_cast at h
      refine ⟨2, by norm_num, ?_⟩
      have hsq : (α - 1) ^ 2 = 0 := by linear_combination h
      have h1 : α - 1 = 0 := by
        have : (α - 1) * (α - 1) = 0 := by simpa [pow_two] using hsq
        exact mul_self_eq_zero.mp this
      have hα : α = 1 := sub_eq_zero.mp h1
      rw [hα]; norm_num
    · -- t = -1: α ^ 2 - α + 1 = 0, so α ^ 6 = 1
      rw [h2] at h; push_cast at h
      refine ⟨6, by norm_num, ?_⟩
      have h6 : α ^ 6 - 1 = 0 := by
        linear_combination (α ^ 4 + α ^ 3 - α - 1) * h
      exact sub_eq_zero.mp h6
    · -- t = 0: α ^ 2 + 1 = 0, so α ^ 4 = 1
      rw [h2] at h; push_cast at h
      refine ⟨4, by norm_num, ?_⟩
      have h4 : α ^ 4 - 1 = 0 := by linear_combination (α ^ 2 - 1) * h
      exact sub_eq_zero.mp h4
    · -- t = 1: α ^ 2 + α + 1 = 0, so α ^ 3 = 1
      rw [h2] at h; push_cast at h
      refine ⟨3, by norm_num, ?_⟩
      have h3 : α ^ 3 - 1 = 0 := by linear_combination (α - 1) * h
      exact sub_eq_zero.mp h3
    · -- t = 2: (α + 1) ^ 2 = 0, so α = -1
      rw [h2] at h; push_cast at h
      refine ⟨2, by norm_num, ?_⟩
      have hsq : (α + 1) ^ 2 = 0 := by linear_combination h
      have h1 : α + 1 = 0 := by
        have : (α + 1) * (α + 1) = 0 := by simpa [pow_two] using hsq
        exact mul_self_eq_zero.mp this
      have hα : α = -1 := eq_neg_of_add_eq_zero_left h1
      rw [hα]; norm_num
  · -- s = -1, t = 0: α ^ 2 - 1 = 0, so α ^ 2 = 1
    rw [hs, ht] at h; push_cast at h
    refine ⟨2, by norm_num, ?_⟩
    have h2 : α ^ 2 - 1 = 0 := by linear_combination h
    exact sub_eq_zero.mp h2

end Work.BW
