import Mathlib
import Submission.Work.Pert.pert2v2.steps

/-!
# `Work.Pert.pert2v2.walkY2`: the deep threshold of the right walk

The right walk of `walk_right_deep` starts at `z ∈ Qm Ξ α` with `z.im ≤ -Y₂`, `x₀ + 3 ≤ z.re`
and walks backwards (`hbwd`) while the left margin `margA_g` stays `≥ 5/4`.  The margin loses at
most `17/16` per step (`margA_step_le`) and the walk needs `≈ 32 (z.re - x₀ - 3)/31` steps, so
the walk is legal as soon as

  `margA_g Ξ α z ≥ 5/4 + (17/16) * 32 (z.re - x₀ - 3)/31`.

Inside the gate, `margA_g Ξ α z ≥ z.re - z.im + (1/α).re - |Ξ| - |(1/α).im|` and
`|z.im| > z.re + Ξ` (`margB_g > 0`), so the inequality holds as soon as `-z.im ≥ Y₂` with `Y₂`
the explicit constant below: `margA_deep_bound` is exactly that statement.

The constant is generous; only its existence matters.
-/

namespace Work.Pert.pert2v2

noncomputable section

/-- The deep threshold of the right walk (a generous constant; only positivity and the
inequality `margA_deep_bound` matter). -/
def walkY2 (Ξ x₀ : ℝ) (α : ℂ) : ℝ := 16 * (|x₀| + |Ξ| + ‖(1 : ℂ) / α‖ + 4) + 16

theorem walkY2_pos (Ξ x₀ : ℝ) (α : ℂ) : 0 < walkY2 Ξ x₀ α := by
  unfold walkY2
  have h1 : (0 : ℝ) ≤ ‖(1 : ℂ) / α‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ |x₀| := abs_nonneg _
  have h3 : (0 : ℝ) ≤ |Ξ| := abs_nonneg _
  linarith

end

end Work.Pert.pert2v2
