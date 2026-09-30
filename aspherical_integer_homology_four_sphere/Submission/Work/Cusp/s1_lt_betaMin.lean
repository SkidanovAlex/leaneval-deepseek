import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- The horotorus level `s₁ = 11/10` is below the minimal ceiling height `βMin = √(3/2)`:
`(11/10)² = 121/100 < 150/100 = 3/2`, so `11/10 < √(3/2)` by monotonicity of the square root
(this is constraint (iii) of the blueprint: every facet of `Q̄` other than the truncation tori has
height `< s₁ < min β`). -/
theorem s1_lt_betaMin : s1 < betaMin := by
  rw [s1, betaMin]
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

end Work.Cusp
