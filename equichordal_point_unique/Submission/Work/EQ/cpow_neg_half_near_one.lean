import Mathlib
import Submission.Work.EQ.SqrtNearOne

/-!
# `(1+z)^(-1/2)` is `2`-Lipschitz at `z = 0`

For `‖z‖ ≤ 1/2` we have `‖(1+z)^(-1/2) - 1‖ ≤ 2‖z‖`, where the power is the principal
branch `Complex.cpow`.

The proof rewrites `(1+z)^(-1/2) = ((1+z)^(1/2))⁻¹ = (sqHalf z)⁻¹`, which is
unconditional via `Complex.cpow_mul_int`, and combines the 1-Lipschitz bound
`‖sqHalf z - 1‖ ≤ ‖z‖` from `SqrtNearOne` with the lower bound `‖sqHalf z‖ ≥ 1/2`
(which follows from `1/2 ≤ Re (sqHalf z) ≤ ‖sqHalf z‖`).
-/

namespace Work.EQ

theorem cpow_neg_half_near_one {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖(1 + z) ^ (-(1 / 2) : ℂ) - 1‖ ≤ 2 * ‖z‖ := by
  have hz1 : ‖z‖ < 1 := by linarith
  -- rewrite the `-1/2` power as the inverse of the principal square root
  have hone : (1 + z) ^ (-(1 / 2) : ℂ) = (sqHalf z)⁻¹ := by
    rw [sqHalf]
    have h : (-(1 / 2) : ℂ) = (1 / 2 : ℂ) * ((-1 : ℤ) : ℂ) := by norm_num
    rw [h, Complex.cpow_mul_int]
    simp
  rw [hone]
  -- the square root moves `1` by at most `‖z‖`
  have hsub : ‖sqHalf z - 1‖ ≤ ‖z‖ := norm_sqHalf_sub_one_le hz1
  have hne : sqHalf z ≠ 0 := by
    intro h
    have h1 := sqHalf_re_pos hz1
    rw [h] at h1
    norm_num at h1
  -- and its real part is at least `1/2`, hence so is its norm
  have hre : (1 / 2 : ℝ) ≤ (sqHalf z).re := by
    have h4 : |(sqHalf z).re - 1| ≤ ‖sqHalf z - 1‖ := by
      simpa using Complex.abs_re_le_norm (sqHalf z - 1)
    have h6 : |(sqHalf z).re - 1| ≤ ‖z‖ := le_trans h4 hsub
    linarith [(abs_le.mp h6).1]
  have hnorm : (1 / 2 : ℝ) ≤ ‖sqHalf z‖ := le_trans hre (Complex.re_le_norm _)
  have hpos : (0 : ℝ) < ‖sqHalf z‖ := by linarith
  have heq : (sqHalf z)⁻¹ - 1 = -(sqHalf z - 1) * (sqHalf z)⁻¹ := by
    field_simp
    ring
  rw [heq, norm_mul, norm_neg, norm_inv, ← div_eq_mul_inv, div_le_iff₀ hpos]
  nlinarith [hsub, hnorm, norm_nonneg z]

end Work.EQ
