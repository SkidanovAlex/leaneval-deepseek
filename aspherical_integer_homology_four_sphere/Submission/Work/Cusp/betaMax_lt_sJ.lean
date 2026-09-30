import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- The ceiling is bounded by `βMax = 3/2`, which is strictly below the junction height
`s_J = e^{1/2}`: indeed `3/2 = 1 + 1/2 < e^{1/2}` by the standard estimate `1 + x < e^x`
for `x ≠ 0`.  Hence every truncation height is below the junction `s_J`, as required in
blueprint §1 for the inner chart to sit below the collar. -/
theorem betaMax_lt_sJ : betaMax < sJ := by
  rw [betaMax, sJ]
  have h := Real.add_one_lt_exp (x := (1 : ℝ) / 2) (by norm_num)
  linarith

end Work.Cusp
