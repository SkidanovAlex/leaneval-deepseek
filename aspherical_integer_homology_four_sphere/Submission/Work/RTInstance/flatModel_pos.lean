import Mathlib
import Submission.Work.RTInstance.Models

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTInstance

/-- The coefficient vector of the flat model: `![1, 1, h₀ ^ 2, h₀ ^ 2]` is positive. -/
theorem flatModel_coeff_pos (h₀ : ℝ) (h0 : h₀ ≠ 0) :
    ∀ i : Fin 4, 0 < ![1, 1, h₀ ^ 2, h₀ ^ 2] i := by
  intro i
  fin_cases i <;> simp [sq_pos_of_ne_zero h0]

/-- **The flat core model is positive definite**: for `h₀ ≠ 0` and `v ≠ 0`,
`flatModel h₀ q v v = v 0 ^ 2 + v 1 ^ 2 + h₀ ^ 2 * (v 2 ^ 2 + v 3 ^ 2) > 0`. -/
theorem flatModel_pos (h₀ : ℝ) (h0 : h₀ ≠ 0) (q : E4) (v : E4) (hv : v ≠ 0) :
    0 < flatModel h₀ q v v :=
  diagQuad_pos (flatModel_coeff_pos h₀ h0) v hv

end Work.RTInstance
