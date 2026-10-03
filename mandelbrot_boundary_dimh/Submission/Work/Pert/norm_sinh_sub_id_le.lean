import Mathlib

namespace Work.Pert

/-- **Taylor estimate for `sinh - id` on the disc of radius `1/2`.**

For `‖w‖ ≤ 1/2`, `‖sinh w - w‖ ≤ ‖w‖³/3`. Writing
`sinh w = (exp w - exp (-w))/2` and expanding both exponentials to order `3`
with `Complex.exp_bound'` (quartic remainder `≤ ‖w‖⁴/12` at each of `±w`) gives

`sinh w - w = w³/6 + (R₊ - R₋)/2`, hence
`‖sinh w - w‖ ≤ ‖w‖³/6 + ‖w‖⁴/12 ≤ ‖w‖³/6 + ‖w‖³/24 < ‖w‖³/3`
using `‖w‖ ≤ 1/2`. -/
theorem norm_sinh_sub_id_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖Complex.sinh w - w‖ ≤ ‖w‖ ^ 3 / 3 := by
  have hnorm : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hfac : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num
  -- Quartic Taylor remainder of `exp` at `w`.
  have hb1 : ‖Complex.exp w - (1 + w + w ^ 2 / 2 + w ^ 3 / 6)‖ ≤ ‖w‖ ^ 4 / 12 := by
    have h := Complex.exp_bound' (x := w) (n := 4) (by
      rw [show ((4 : ℕ).succ : ℝ) = 5 by norm_num]; linarith)
    have hs : (∑ m ∈ Finset.range 4, w ^ m / (m.factorial : ℂ))
        = 1 + w + w ^ 2 / 2 + w ^ 3 / 6 := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [hs, hfac] at h
    nlinarith [h]
  -- Quartic Taylor remainder of `exp` at `-w`.
  have hb2 : ‖Complex.exp (-w) - (1 + (-w) + (-w) ^ 2 / 2 + (-w) ^ 3 / 6)‖ ≤ ‖w‖ ^ 4 / 12 := by
    have h := Complex.exp_bound' (x := -w) (n := 4) (by
      rw [show ((4 : ℕ).succ : ℝ) = 5 by norm_num, norm_neg]; linarith)
    have hs : (∑ m ∈ Finset.range 4, (-w) ^ m / (m.factorial : ℂ))
        = 1 + (-w) + (-w) ^ 2 / 2 + (-w) ^ 3 / 6 := by
      simp [Finset.sum_range_succ, Nat.factorial]
    rw [hs, hfac, norm_neg] at h
    nlinarith [h]
  -- The exact identity expressing `sinh w - w` through the two remainders.
  have hid : Complex.sinh w - w
      = w ^ 3 / 6 + ((Complex.exp w - (1 + w + w ^ 2 / 2 + w ^ 3 / 6))
          - (Complex.exp (-w) - (1 + (-w) + (-w) ^ 2 / 2 + (-w) ^ 3 / 6))) / 2 := by
    rw [Complex.sinh]; ring
  have hA : ‖w ^ 3 / 6‖ ≤ ‖w‖ ^ 3 / 6 := by
    rw [Complex.norm_div, Complex.norm_pow]; norm_num
  have hB : ‖((Complex.exp w - (1 + w + w ^ 2 / 2 + w ^ 3 / 6))
        - (Complex.exp (-w) - (1 + (-w) + (-w) ^ 2 / 2 + (-w) ^ 3 / 6))) / 2‖
      ≤ (‖w‖ ^ 4 / 12 + ‖w‖ ^ 4 / 12) / 2 := by
    rw [Complex.norm_div]
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact (norm_sub_le _ _).trans (by linarith [hb1, hb2])
  calc ‖Complex.sinh w - w‖
      = ‖w ^ 3 / 6 + ((Complex.exp w - (1 + w + w ^ 2 / 2 + w ^ 3 / 6))
          - (Complex.exp (-w) - (1 + (-w) + (-w) ^ 2 / 2 + (-w) ^ 3 / 6))) / 2‖ := by rw [hid]
    _ ≤ ‖w ^ 3 / 6‖ + ‖((Complex.exp w - (1 + w + w ^ 2 / 2 + w ^ 3 / 6))
          - (Complex.exp (-w) - (1 + (-w) + (-w) ^ 2 / 2 + (-w) ^ 3 / 6))) / 2‖ := norm_add_le _ _
    _ ≤ ‖w‖ ^ 3 / 6 + (‖w‖ ^ 4 / 12 + ‖w‖ ^ 4 / 12) / 2 := add_le_add hA hB
    _ ≤ ‖w‖ ^ 3 / 3 := by nlinarith [hw, hnorm, pow_nonneg hnorm 3]

end Work.Pert
