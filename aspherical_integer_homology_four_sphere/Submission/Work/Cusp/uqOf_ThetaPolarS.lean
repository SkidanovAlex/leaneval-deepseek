import Mathlib
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.invY_wOf

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

open scoped Real InnerProductSpace

/-- The `w`-coordinates of `ThetaPolarS v c p y` are `wOf v y`, so the `invY`-recovery of `y` in
`uqOf` returns `y` (`invY_wOf`). -/
private theorem invY_w_part (v : Fin 5) (c : ℝ) (p y : E2) :
    invY v (!₂[ThetaPolarS v c p y 2, ThetaPolarS v c p y 3] : E2) = y := by
  have h : (!₂[ThetaPolarS v c p y 2, ThetaPolarS v c p y 3] : E2) = wOf v y := by
    ext i; fin_cases i <;> simp [ThetaPolarS]
  rw [h, invY_wOf]

/-- **The perimeter coordinate of the shifted polar chart.**  `uqOf` inverts the angle coordinate of
`ThetaPolarS`: the `w`-coordinates determine `y` (`invY_wOf`), the two inner products with `slope v`
cancel, and division by `2π` leaves the shifted lift `uS c p`. -/
theorem uqOf_ThetaPolarS (v : Fin 5) (c : ℝ) (p y : E2) :
    uqOf v (ThetaPolarS v c p y) = uS c p := by
  have hw := invY_w_part v c p y
  have key : (2 * π * uS c p + 2 * π * ⟪cuspY v y, slope v⟫_ℝ / ‖slope v‖ ^ 2
      - 2 * π * ⟪cuspY v (invY v (!₂[ThetaPolarS v c p y 2, ThetaPolarS v c p y 3] : E2)),
          slope v⟫_ℝ / ‖slope v‖ ^ 2) / (2 * π) = uS c p := by
    rw [hw]
    field_simp
    ring
  simpa [uqOf, ThetaPolarS] using key

end Work.Cusp
