import Mathlib

namespace Work.Resample

/-- The basic secant-slope estimate for `exp`: `exp x - 1 ≤ x * exp x` for every real `x`
(equivalently `1 - exp (-x) ≤ x`, which is `Real.add_one_le_exp`). -/
lemma exp_sub_one_le_mul_exp (x : ℝ) : Real.exp x - 1 ≤ x * Real.exp x := by
  have h : 1 - Real.exp (-x) ≤ x := by
    have := Real.add_one_le_exp (-x)
    linarith
  have h2 : Real.exp x * (1 - Real.exp (-x)) ≤ Real.exp x * x :=
    mul_le_mul_of_nonneg_left h (Real.exp_pos x).le
  have heq : Real.exp x * (1 - Real.exp (-x)) = Real.exp x - 1 := by
    have hmul : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith [hmul]
  rw [heq] at h2
  linarith [h2]

/-- `|exp a - exp b| ≤ exp (max a b) * |a - b|`: `exp` is Lipschitz on the interval between
`a` and `b` with the constant `exp (max a b)` (the maximal value of the derivative there). -/
theorem absExpSubLeExpMax (a b : ℝ) : |Real.exp a - Real.exp b| ≤ Real.exp (max a b) * |a - b| := by
  rcases le_total a b with h | h
  · have hmax : max a b = b := max_eq_right h
    have habs : |a - b| = b - a := by
      rw [abs_of_nonpos (by linarith)]
      ring
    have h1 : |Real.exp a - Real.exp b| = Real.exp b - Real.exp a := by
      rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr h))]
      ring
    rw [h1, hmax, habs]
    have hfact : Real.exp b - Real.exp a = Real.exp a * (Real.exp (b - a) - 1) := by
      have hab : Real.exp a * Real.exp (b - a) = Real.exp b := by
        rw [← Real.exp_add]; ring_nf
      nlinarith [hab]
    calc Real.exp b - Real.exp a
        = Real.exp a * (Real.exp (b - a) - 1) := hfact
      _ ≤ Real.exp a * ((b - a) * Real.exp (b - a)) :=
            mul_le_mul_of_nonneg_left (exp_sub_one_le_mul_exp (b - a)) (Real.exp_pos a).le
      _ = Real.exp b * (b - a) := by
            have hab : Real.exp a * Real.exp (b - a) = Real.exp b := by
              rw [← Real.exp_add]; ring_nf
            calc Real.exp a * ((b - a) * Real.exp (b - a))
                = (Real.exp a * Real.exp (b - a)) * (b - a) := by ring
              _ = Real.exp b * (b - a) := by rw [hab]
  · have hmax : max a b = a := max_eq_left h
    have habs : |a - b| = a - b := by
      rw [abs_of_nonneg (by linarith)]
    have h1 : |Real.exp a - Real.exp b| = Real.exp a - Real.exp b := by
      rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h))]
    rw [h1, hmax, habs]
    have hfact : Real.exp a - Real.exp b = Real.exp b * (Real.exp (a - b) - 1) := by
      have hab : Real.exp b * Real.exp (a - b) = Real.exp a := by
        rw [← Real.exp_add]; ring_nf
      nlinarith [hab]
    calc Real.exp a - Real.exp b
        = Real.exp b * (Real.exp (a - b) - 1) := hfact
      _ ≤ Real.exp b * ((a - b) * Real.exp (a - b)) :=
            mul_le_mul_of_nonneg_left (exp_sub_one_le_mul_exp (a - b)) (Real.exp_pos b).le
      _ = Real.exp a * (a - b) := by
            have hab : Real.exp b * Real.exp (a - b) = Real.exp a := by
              rw [← Real.exp_add]; ring_nf
            calc Real.exp b * ((a - b) * Real.exp (a - b))
                = (Real.exp b * Real.exp (a - b)) * (a - b) := by ring
              _ = Real.exp a * (a - b) := by rw [hab]

end Work.Resample
