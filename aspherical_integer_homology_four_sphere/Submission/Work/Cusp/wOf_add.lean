import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

open scoped Real InnerProductSpace

/-- `wOf` is additive: the `w`-coordinates of `y` are the coordinates of the linear map
`y ↦ y₂λ₂ + y₃λ₃` followed by the orthogonal projections onto the orthonormal frame
`(frame2, frame3)` of `σ^⊥`, and both steps are additive. -/
theorem wOf_add (v : Fin 5) (y y' : E2) : wOf v (y + y') = wOf v y + wOf v y' := by
  simp [wOf, cuspY, add_smul, inner_add_left]
  ext i
  fin_cases i <;> simp <;> ring

end Work.Cusp
