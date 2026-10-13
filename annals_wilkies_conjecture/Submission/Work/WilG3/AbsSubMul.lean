import Mathlib

namespace Work.WilG3

theorem AbsSubMul {a b C : ℝ} (ha : |a| < C) (hb : |b| < C) (hab : 0 ≤ a * b) :
    |a - b| < C := by
  have hmax : max |a| |b| < C := max_lt ha hb
  have key : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y → |x - y| ≤ max |x| |y| := by
    intro x y hx hy
    rw [abs_sub_le_iff]
    constructor
    · calc x - y ≤ x := by linarith
        _ ≤ |x| := le_abs_self x
        _ ≤ max |x| |y| := le_max_left _ _
    · calc y - x ≤ y := by linarith
        _ ≤ |y| := le_abs_self y
        _ ≤ max |x| |y| := le_max_right _ _
  rcases le_or_gt 0 a with ha0 | ha0
  · rcases le_or_gt 0 b with hb0 | hb0
    · exact lt_of_le_of_lt (key ha0 hb0) hmax
    · -- a ≥ 0 and b < 0 force a * b ≤ 0, so a * b = 0 and a = 0
      have h1 : a * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha0 (le_of_lt hb0)
      have h2 : a * b = 0 := le_antisymm h1 hab
      have haz : a = 0 := (mul_eq_zero.mp h2).resolve_right (ne_of_lt hb0)
      rw [haz, zero_sub, abs_neg]
      exact hb
  · -- a < 0 forces b ≤ 0, then both signs are nonpositive
    have hb0 : b ≤ 0 := by
      by_contra h
      push Not at h
      have : a * b < 0 := mul_neg_of_neg_of_pos ha0 h
      linarith
    have h := key (neg_nonneg.mpr (le_of_lt ha0)) (neg_nonneg.mpr hb0)
    have h' : |a - b| ≤ max |a| |b| := by
      have e : (-a : ℝ) - -b = -(a - b) := by ring
      simpa [e, abs_neg, abs_sub_comm] using h
    exact lt_of_le_of_lt h' hmax

end Work.WilG3
