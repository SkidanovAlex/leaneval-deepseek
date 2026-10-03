import Mathlib

namespace Work.Pert

/-- **Numerical bound for the ratio `(exp z - 1)/z` on the disc of radius `1/2`.**

For `z ≠ 0` with `‖z‖ ≤ 1/2`,
`‖(exp z - 1)/z - 1‖ ≤ 11/36`.

The quantity is `(exp z - 1 - z)/z = z/2 + z²/6 + z³/24 + …`; the optimal bound on the
disc of radius `1/2` is `2 (e^{1/2} - 3/2) ≈ 0.2974`, and `11/36 ≈ 0.3056` is a rational
value slightly above it, convenient as a perturbation constant.

Proof: `Complex.exp_bound'` with `n = 4` (legitimate since `‖z‖/5 ≤ 1/2`) gives
`‖exp z - (1 + z + z²/2 + z³/6)‖ ≤ ‖z‖⁴/24 · 2 = ‖z‖⁴/12`, whence
`‖exp z - 1 - z‖ ≤ ‖z‖⁴/12 + ‖z‖²/2 + ‖z‖³/6`, and dividing by `‖z‖ ≤ 1/2` gives
`‖z‖³/12 + ‖z‖/2 + ‖z‖²/6 ≤ 1/96 + 1/4 + 1/24 = 29/96 ≤ 11/36`. -/
theorem norm_ratio_exp_sub_one_le {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ ≤ 1 / 2) :
    ‖(Complex.exp z - 1) / z - 1‖ ≤ 11 / 36 := by
  have hr0 : 0 < ‖z‖ := by rw [norm_pos_iff]; exact hz0
  -- `(exp z - 1)/z - 1 = (exp z - 1 - z)/z`
  have hmain : (Complex.exp z - 1) / z - 1 = (Complex.exp z - 1 - z) / z := by
    field_simp
  rw [hmain, Complex.norm_div]
  -- Taylor bound with `n = 4`: the tail is at most `‖z‖⁴/4! · 2 = ‖z‖⁴/12`.
  have hb := Complex.exp_bound' (x := z) (n := 4) (by push_cast; linarith)
  have hsum : (∑ m ∈ Finset.range 4, z ^ m / ((m.factorial : ℕ) : ℂ))
      = 1 + z + z ^ 2 / 2 + z ^ 3 / 6 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at hb
  -- Bound the numerator `exp z - 1 - z`.
  have hbound : ‖Complex.exp z - 1 - z‖ ≤ ‖z‖ ^ 4 / 12 + ‖z‖ ^ 2 / 2 + ‖z‖ ^ 3 / 6 := by
    have hid : Complex.exp z - 1 - z
        = (Complex.exp z - (1 + z + z ^ 2 / 2 + z ^ 3 / 6)) + (z ^ 2 / 2 + z ^ 3 / 6) := by ring
    rw [hid]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖z ^ 2 / 2 + z ^ 3 / 6‖ ≤ ‖z‖ ^ 2 / 2 + ‖z‖ ^ 3 / 6 := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_div, Complex.norm_div, Complex.norm_pow, Complex.norm_pow]
      norm_num
    have h4 : ‖z‖ ^ 4 / ↑(Nat.factorial 4) * 2 = ‖z‖ ^ 4 / 12 := by
      rw [show (Nat.factorial 4 : ℝ) = 24 by norm_num]
      ring
    rw [h4] at hb
    linarith
  -- Divide by `‖z‖` and use `‖z‖ ≤ 1/2`.
  have hXr : (‖z‖ ^ 4 / 12 + ‖z‖ ^ 2 / 2 + ‖z‖ ^ 3 / 6) / ‖z‖ ≤ 11 / 36 := by
    have heq : (‖z‖ ^ 4 / 12 + ‖z‖ ^ 2 / 2 + ‖z‖ ^ 3 / 6) / ‖z‖
        = ‖z‖ ^ 3 / 12 + ‖z‖ / 2 + ‖z‖ ^ 2 / 6 := by
      field_simp
    rw [heq]
    nlinarith [sq_nonneg ‖z‖, norm_nonneg z]
  exact (div_le_div_of_nonneg_right hbound hr0.le).trans hXr

end Work.Pert
