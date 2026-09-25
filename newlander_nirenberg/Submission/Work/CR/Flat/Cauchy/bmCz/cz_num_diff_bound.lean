import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCz.cz_num_core
import Submission.Work.CR.Flat.Cauchy.bmCz.cz_real_core

namespace Work.CR.Flat.Cauchy.bmCz

/-- Coordinate-free form of the difference quotient: bring the two terms to a
common denominator `X^m * Y^m`. -/
theorem cz_num_diff_bound {m : ℕ} (hm : 2 ≤ m) {X Y H : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hH : 0 ≤ H) (hXY : |X - Y| ≤ H)
    (hYe : X ≤ 2 * Y) (hYu : 2 * Y ≤ 3 * X)
    {A B : ℂ} (hB : ‖B‖ ≤ Y ^ 2) (hAB : ‖A - B‖ ≤ (5 / 2) * X * H) :
    ‖A / ((X : ℂ) ^ m) - B / ((Y : ℂ) ^ m)‖
      ≤ (5 / 2 + (m : ℝ) * (3 / 2) ^ (m - 1) * 2 ^ (m - 2)) * H / X ^ (m - 1) := by
  have hXm : (0 : ℝ) < X ^ m := pow_pos hX m
  have hYm : (0 : ℝ) < Y ^ m := pow_pos hY m
  have hden : (0 : ℝ) < X ^ m * Y ^ m := mul_pos hXm hYm
  have hneX : (((X ^ m : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hXm)
  have hneY : (((Y ^ m : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hYm)
  have hnormden : ‖(((X ^ m : ℝ)) : ℂ) * (((Y ^ m : ℝ)) : ℂ)‖ = X ^ m * Y ^ m := by
    rw [← Complex.ofReal_mul]
    exact (RCLike.norm_ofReal (X ^ m * Y ^ m)).trans (abs_of_nonneg (le_of_lt hden))
  have hident : A / ((X : ℂ) ^ m) - B / ((Y : ℂ) ^ m)
      = (A * ((Y ^ m : ℝ) : ℂ) - B * ((X ^ m : ℝ) : ℂ))
          / ((((X ^ m : ℝ)) : ℂ) * (((Y ^ m : ℝ)) : ℂ)) := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow]
    rw [div_sub_div A B hneX hneY]
    ring
  rw [hident, norm_div, hnormden]
  calc ‖A * ((Y ^ m : ℝ) : ℂ) - B * ((X ^ m : ℝ) : ℂ)‖ / (X ^ m * Y ^ m)
      ≤ (5 / 2) * X * H / X ^ m
          + (m : ℝ) * (3 * X / 2) ^ (m - 1) * H * Y ^ 2 / (X ^ m * Y ^ m) :=
        cz_num_core hm hX hY hH hXY hYu hB hAB
    _ ≤ (5 / 2 + (m : ℝ) * (3 / 2) ^ (m - 1) * 2 ^ (m - 2)) * H * (X ^ (m - 1))⁻¹ :=
        cz_real_core hm hX hY hH hXY hYe hYu
    _ = (5 / 2 + (m : ℝ) * (3 / 2) ^ (m - 1) * 2 ^ (m - 2)) * H / X ^ (m - 1) := by
        simp only [div_eq_mul_inv]

end Work.CR.Flat.Cauchy.bmCz
