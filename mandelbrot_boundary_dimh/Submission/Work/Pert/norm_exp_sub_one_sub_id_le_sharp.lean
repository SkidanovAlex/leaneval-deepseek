import Mathlib

namespace Work.Pert

/-- **Sharp Taylor estimate for `exp` on the disc of radius `1/2`.**

For `‖z‖ ≤ 1/2`, `‖exp z - 1 - z‖ ≤ 29/48 · ‖z‖²`. The constant `29/48` is exactly
`1/2 + 1/12 + 1/48`, obtained by splitting `exp z - 1 - z` into the quartic Taylor tail
(bounded by `‖z‖⁴/12`, using `Complex.exp_bound'` with `n = 4`) and the explicit terms
`z²/2 + z³/6` (bounded by `‖z‖²/2 + ‖z‖²/12`, since `‖z‖ ≤ 1/2`). The bound is attained
at `‖z‖ = 1/2`, where the tail bound and `z³/6` are both saturated in the worst direction. -/
theorem norm_exp_sub_one_sub_id_le_sharp {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.exp z - 1 - z‖ ≤ 29 / 48 * ‖z‖ ^ 2 := by
  have hr : 0 ≤ ‖z‖ := norm_nonneg z
  -- Quartic Taylor bound: `‖exp z - (1 + z + z²/2 + z³/6)‖ ≤ ‖z‖⁴/12`.
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
  -- `‖z‖ ≤ 1/2` collapses the higher powers: `‖z‖³ ≤ ‖z‖²/2` and `‖z‖⁴ ≤ ‖z‖²/4`.
  have hsq : ‖z‖ ^ 2 ≤ 1 / 4 := by
    have h := mul_self_le_mul_self hr hz
    nlinarith [h]
  have h3 : ‖z‖ ^ 3 ≤ ‖z‖ ^ 2 / 2 := by
    calc ‖z‖ ^ 3 = ‖z‖ ^ 2 * ‖z‖ := by ring
      _ ≤ ‖z‖ ^ 2 * (1 / 2) := mul_le_mul_of_nonneg_left hz (sq_nonneg _)
      _ = ‖z‖ ^ 2 / 2 := by ring
  have h4le : ‖z‖ ^ 4 ≤ ‖z‖ ^ 2 / 4 := by
    calc ‖z‖ ^ 4 = ‖z‖ ^ 2 * ‖z‖ ^ 2 := by ring
      _ ≤ ‖z‖ ^ 2 * (1 / 4) := mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
      _ = ‖z‖ ^ 2 / 4 := by ring
  linarith

end Work.Pert
