import Mathlib
import Submission.Work.Escape.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Escape

/-- Escape step: once `‖z‖ ≥ 2` and the growth constant satisfies `A ≤ ‖z‖` (in particular once
`‖z‖ ≥ max 2 A`), the orbit norm does not decrease: `‖z‖ ≤ ‖f z‖`.  This is the sharp escape
criterion in its first step; iterating it gives monotone growth of the orbit norms. -/
theorem escape_step (f : ℂ → ℂ) (d : ℕ) (A : ℝ) (h : MonicGrowth f d A) (hd : 2 ≤ d)
    {z : ℂ} (hz : 2 ≤ ‖z‖) (hA : A ≤ ‖z‖) : ‖z‖ ≤ ‖f z‖ := by
  -- `‖z‖ ^ d ≥ 2 ‖z‖` since `d ≥ 2` and `‖z‖ ≥ 2`.
  have h1 : ‖z‖ ^ 2 ≤ ‖z‖ ^ d := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ ‖z‖) hd
  have h2 : 2 * ‖z‖ ≤ ‖z‖ ^ d := by nlinarith [sq_nonneg ‖z‖, h1, hz]
  -- `‖z‖ ≤ ‖z‖ ^ d - A` using `A ≤ ‖z‖`, and `‖z‖ ^ d - A ≤ ‖f z‖` by monic growth.
  have h3 := h.le_norm z
  nlinarith [h3, hA, h2]

end Work.Escape
