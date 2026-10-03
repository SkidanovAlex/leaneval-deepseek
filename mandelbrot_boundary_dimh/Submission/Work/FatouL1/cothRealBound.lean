import Mathlib

namespace Work.FatouL1

/-- The elementary bound `y * exp (-y) ≤ sinh y`, valid for every real `y`; for `y > 0` it is
the upper bound on `coth y - 1/y`.  It is `Real.add_one_le_exp` at `2 * y`. -/
private lemma mul_exp_neg_le_sinh (y : ℝ) : y * Real.exp (-y) ≤ Real.sinh y := by
  have h : (2 * y + 1) * Real.exp (-y) ≤ Real.exp y := by
    have h1 : (2 * y + 1) * Real.exp (-y) ≤ Real.exp (2 * y) * Real.exp (-y) :=
      mul_le_mul_of_nonneg_right (Real.add_one_le_exp (2 * y)) (Real.exp_nonneg (-y))
    calc (2 * y + 1) * Real.exp (-y) ≤ Real.exp (2 * y) * Real.exp (-y) := h1
      _ = Real.exp (2 * y - y) := by rw [← Real.exp_add]; ring_nf
      _ = Real.exp y := by ring_nf
  have h2 : 2 * (y * Real.exp (-y)) ≤ Real.exp y - Real.exp (-y) := by
    nlinarith [h, Real.exp_pos (-y)]
  rw [Real.sinh_eq]
  linarith

/-- The elementary bound `sinh y ≤ y * exp y`, valid for every real `y`; for `y > 0` it is the
lower bound on `coth y - 1/y`.  It is `Real.add_one_le_exp` at `-2 * y`. -/
private lemma sinh_le_mul_exp (y : ℝ) : Real.sinh y ≤ y * Real.exp y := by
  have h1 : 1 - Real.exp (-(2 * y)) ≤ 2 * y := by
    have := Real.add_one_le_exp (-(2 * y)); linarith
  rw [Real.sinh_eq]
  have he := Real.exp_pos (-y)
  have hey := Real.exp_pos y
  have hmul : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  have he2 : Real.exp (-(2 * y)) = Real.exp (-y) * Real.exp (-y) := by
    rw [← Real.exp_add]; ring_nf
  nlinarith [h1, he, hey, hmul, he2]

/-- `‖coth y - 1/y‖ ≤ 1` for `y > 0`. -/
private lemma coth_bound_pos {y : ℝ} (hy : 0 < y) :
    ‖Real.cosh y / Real.sinh y - 1 / y‖ ≤ 1 := by
  have hs : 0 < Real.sinh y := Real.sinh_pos_iff.mpr hy
  have hD : 0 < y * Real.sinh y := mul_pos hy hs
  have hQ : Real.cosh y / Real.sinh y - 1 / y
      = (y * Real.cosh y - Real.sinh y) / (y * Real.sinh y) := by
    have hs' : Real.sinh y ≠ 0 := ne_of_gt hs
    field_simp
  have key1 : y * Real.exp (-y) ≤ Real.sinh y := mul_exp_neg_le_sinh y
  have key2 : Real.sinh y ≤ y * Real.exp y := sinh_le_mul_exp y
  have hcs : Real.cosh y - Real.sinh y = Real.exp (-y) := Real.cosh_sub_sinh y
  have hcs2 : Real.cosh y + Real.sinh y = Real.exp y := Real.cosh_add_sinh y
  rw [hQ, Real.norm_eq_abs, abs_le]
  constructor
  · rw [le_div_iff₀ hD]
    nlinarith [key2, hcs2]
  · rw [div_le_iff₀ hD]
    nlinarith [key1, hcs]

/-- `coth` is odd, so the bound for `y < 0` follows from the one for `-y > 0`. -/
private lemma coth_diff_neg (y : ℝ) :
    Real.cosh y / Real.sinh y - 1 / y
      = -(Real.cosh (-y) / Real.sinh (-y) - 1 / (-y)) := by
  rw [Real.cosh_neg, Real.sinh_neg]
  by_cases hy0 : y = 0
  · subst hy0; simp
  · field_simp
    ring

theorem cothRealBound : ∀ y : ℝ, y ≠ 0 → ‖Real.cosh y / Real.sinh y - 1 / y‖ ≤ 1 := by
  intro y hy
  rcases lt_or_gt_of_ne hy with h | h
  · have hz : 0 < -y := neg_pos.mpr h
    have hbound := coth_bound_pos hz
    rw [coth_diff_neg y, norm_neg]
    exact hbound
  · exact coth_bound_pos h

end Work.FatouL1
