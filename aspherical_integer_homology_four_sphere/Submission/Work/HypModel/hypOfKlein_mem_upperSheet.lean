import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

open scoped Matrix InnerProductSpace
open Matrix

/-- The Klein lift of a point of the unit ball lands on the upper sheet of the hyperboloid:
`(y,1)/√(1−|y|²)` is timelike of norm `−1` with positive last coordinate. -/
theorem hypOfKlein_mem_upperSheet {y : E4} (hy : y ∈ ball) : hypOfKlein y ∈ upperSheet := by
  have hy' : ‖y‖ < 1 := hy
  have h1 : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
  have hs : 0 < Real.sqrt (1 - ‖y‖ ^ 2) := Real.sqrt_pos.mpr h1
  refine ⟨?_, ?_⟩
  · rw [show hypOfKlein y = (Real.sqrt (1 - ‖y‖ ^ 2))⁻¹ • ray y from rfl]
    rw [lorentz_smul_left, lorentz_smul_right, lorentz_ray_self]
    set s := Real.sqrt (1 - ‖y‖ ^ 2) with hsdef
    have hs2 : s ^ 2 = 1 - ‖y‖ ^ 2 := by rw [hsdef]; exact Real.sq_sqrt (le_of_lt h1)
    have hsne : s ≠ 0 := by rw [hsdef]; exact ne_of_gt hs
    field_simp
    nlinarith
  · simp only [hypOfKlein_apply_four]
    positivity

end Work.HypModel
