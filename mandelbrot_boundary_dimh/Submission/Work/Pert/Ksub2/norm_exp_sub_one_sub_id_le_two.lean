import Mathlib

namespace Work.Pert.Ksub2

/-- **Quadratic Taylor estimate for `exp` on the disc of radius `2`.**

For `‖z‖ ≤ 2`, `‖exp z - 1 - z‖ ≤ 3/2 · ‖z‖²`.  The proof splits
`exp z - 1 - z = (exp z - (1 + z + z²/2 + z³/6)) + (z²/2 + z³/6)`; the four-term
Taylor remainder is bounded by `‖z‖⁴/12` using `Complex.exp_bound'` with `n = 4`
(valid because `‖z‖/5 ≤ 1/2`), and the explicit part by `‖z‖²/2 + ‖z‖³/6`.
Since `‖z‖ ≤ 2` kills the higher powers (`‖z‖³ ≤ 2‖z‖²` and `‖z‖⁴ ≤ 4‖z‖²`), the total
is at most `‖z‖² (1/2 + 1/3 + 1/3) = 7/6 ‖z‖² ≤ 3/2 ‖z‖²`. -/
theorem norm_exp_sub_one_sub_id_le_two {z : ℂ} (hz : ‖z‖ ≤ 2) :
    ‖Complex.exp z - 1 - z‖ ≤ 3 / 2 * ‖z‖ ^ 2 := by
  have hr : 0 ≤ ‖z‖ := norm_nonneg z
  -- `n = 4` Taylor bound: `‖exp z - (1 + z + z²/2 + z³/6)‖ ≤ ‖z‖⁴/12`.
  have hb := Complex.exp_bound' (x := z) (n := 4) (by push_cast; linarith)
  have hsum : (∑ m ∈ Finset.range 4, z ^ m / ((m.factorial : ℕ) : ℂ))
      = 1 + z + z ^ 2 / 2 + z ^ 3 / 6 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at hb
  have h4 : ‖z‖ ^ 4 / ↑(Nat.factorial 4) * 2 = ‖z‖ ^ 4 / 12 := by
    rw [show (Nat.factorial 4 : ℝ) = 24 by norm_num]; ring
  rw [h4] at hb
  -- Split off the explicit polynomial part.
  have hid : Complex.exp z - 1 - z
      = (Complex.exp z - (1 + z + z ^ 2 / 2 + z ^ 3 / 6)) + (z ^ 2 / 2 + z ^ 3 / 6) := by ring
  rw [hid]
  refine (norm_add_le _ _).trans ?_
  have h2 : ‖z ^ 2 / 2 + z ^ 3 / 6‖ ≤ ‖z‖ ^ 2 / 2 + ‖z‖ ^ 3 / 6 := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_div, Complex.norm_div, Complex.norm_pow, Complex.norm_pow]
    norm_num
  -- `‖z‖ ≤ 2` collapses the higher powers.
  have hsq : ‖z‖ ^ 2 ≤ 4 := by
    have h := mul_self_le_mul_self hr hz
    nlinarith [h]
  have h3 : ‖z‖ ^ 3 / 6 ≤ ‖z‖ ^ 2 / 3 := by nlinarith [hr, hz]
  have h4b : ‖z‖ ^ 4 / 12 ≤ ‖z‖ ^ 2 / 3 := by nlinarith [hsq, sq_nonneg ‖z‖]
  linarith [hb, h2, h3, h4b, sq_nonneg ‖z‖]

end Work.Pert.Ksub2
