import Mathlib

namespace Work.ZeroDensity.Ingham

/-- Raise a product of five nonnegative factors to a real power. -/
lemma mul5_rpow {a b c d e z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (he : 0 ≤ e) : (a * b * c * d * e) ^ z = a ^ z * b ^ z * c ^ z * d ^ z * e ^ z := by
  have h1 : (0 : ℝ) ≤ a * b * c * d := by positivity
  have h2 : (0 : ℝ) ≤ a * b * c := by positivity
  have h3 : (0 : ℝ) ≤ a * b := by positivity
  rw [Real.mul_rpow h1 he, Real.mul_rpow h2 hd, Real.mul_rpow h3 hc, Real.mul_rpow ha hb]

theorem perZero_rpow {Y σ W A B M : ℝ} (hY : 1 ≤ Y)
    (hW : 0 ≤ W) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (h : (1 / 12 : ℝ) ≤ Y ^ ((1 : ℝ) / 2 - σ) * W ^ ((3 : ℝ) / 4) * A ^ ((1 : ℝ) / 4)
            * B ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 4)) :
    (1 / 12 : ℝ) ^ ((4 : ℝ) / 3) ≤
      W * Y ^ ((2 - 4 * σ) / 3) * A ^ ((1 : ℝ) / 3) * M ^ ((1 : ℝ) / 3) * B ^ ((2 : ℝ) / 3) := by
  have hYpos : (0 : ℝ) < Y := by linarith
  have ha : (0 : ℝ) ≤ Y ^ ((1 : ℝ) / 2 - σ) := (Real.rpow_pos_of_pos hYpos _).le
  have hb : (0 : ℝ) ≤ W ^ ((3 : ℝ) / 4) := Real.rpow_nonneg hW _
  have hc : (0 : ℝ) ≤ A ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hA _
  have hd : (0 : ℝ) ≤ B ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hB _
  have he : (0 : ℝ) ≤ M ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hM _
  have key : (Y ^ ((1 : ℝ) / 2 - σ) * W ^ ((3 : ℝ) / 4) * A ^ ((1 : ℝ) / 4)
            * B ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 4)) ^ ((4 : ℝ) / 3)
      = W * Y ^ ((2 - 4 * σ) / 3) * A ^ ((1 : ℝ) / 3) * M ^ ((1 : ℝ) / 3)
          * B ^ ((2 : ℝ) / 3) := by
    rw [mul5_rpow ha hb hc hd he]
    rw [← Real.rpow_mul hYpos.le ((1 : ℝ) / 2 - σ) ((4 : ℝ) / 3),
        ← Real.rpow_mul hW ((3 : ℝ) / 4) ((4 : ℝ) / 3),
        ← Real.rpow_mul hA ((1 : ℝ) / 4) ((4 : ℝ) / 3),
        ← Real.rpow_mul hB ((1 : ℝ) / 2) ((4 : ℝ) / 3),
        ← Real.rpow_mul hM ((1 : ℝ) / 4) ((4 : ℝ) / 3)]
    have e1 : ((1 : ℝ) / 2 - σ) * ((4 : ℝ) / 3) = (2 - 4 * σ) / 3 := by ring
    have e2 : ((3 : ℝ) / 4) * ((4 : ℝ) / 3) = (1 : ℝ) := by norm_num
    have e3 : ((1 : ℝ) / 4) * ((4 : ℝ) / 3) = (1 : ℝ) / 3 := by norm_num
    have e4 : ((1 : ℝ) / 2) * ((4 : ℝ) / 3) = (2 : ℝ) / 3 := by norm_num
    rw [e1, e2, e3, e4, Real.rpow_one]
    ring
  calc (1 / 12 : ℝ) ^ ((4 : ℝ) / 3)
      ≤ (Y ^ ((1 : ℝ) / 2 - σ) * W ^ ((3 : ℝ) / 4) * A ^ ((1 : ℝ) / 4)
            * B ^ ((1 : ℝ) / 2) * M ^ ((1 : ℝ) / 4)) ^ ((4 : ℝ) / 3) :=
        Real.rpow_le_rpow (by norm_num) h (by norm_num)
    _ = W * Y ^ ((2 - 4 * σ) / 3) * A ^ ((1 : ℝ) / 3) * M ^ ((1 : ℝ) / 3)
          * B ^ ((2 : ℝ) / 3) := key

end Work.ZeroDensity.Ingham
