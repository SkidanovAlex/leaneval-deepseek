import Mathlib
import Submission.Work.C17.seventeen_defs

namespace Work.C17I

/-- On the disc `‖z‖ ≤ 34/100`, the symmetrisation variable `yC z = z²/(z−1)` is bounded by
`1/5`:  `‖yC z‖ ≤ (34/100)² / (1 − 34/100) = 289/1650 < 1/5`. -/
theorem yC_norm_lt_fifth (z : ℂ) (hz : ‖z‖ ≤ (34 : ℝ) / 100) :
    ‖Work.C17.yC z‖ < 1 / 5 := by
  -- `‖z - 1‖ ≥ 1 - ‖z‖ ≥ 66/100 > 0`
  have h1 : (1 : ℝ) - ‖z‖ ≤ ‖z - 1‖ := by
    have := norm_sub_norm_le (1 : ℂ) z
    simpa [norm_sub_rev] using this
  have hlt : ‖z‖ < 1 := by linarith
  have hpos : 0 < ‖z - 1‖ := by linarith
  -- the elementary estimate `‖z‖² ≤ (34/100)²`
  have hsq : ‖z‖ ^ 2 ≤ ((34 : ℝ) / 100) ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  rw [Work.C17.yC, norm_div, norm_pow, div_lt_iff₀ hpos]
  nlinarith

end Work.C17I
