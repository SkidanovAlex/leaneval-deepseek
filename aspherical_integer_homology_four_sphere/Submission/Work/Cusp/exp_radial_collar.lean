import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.collarHeight_half

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- On the collar `‖p‖∞ ≥ 1/2` the radial coordinate is `r = R₀ − log s`, where `s = collarS v p y`
is the UHS height of the outer chart; exponentiating recovers `s`.  On the junction layer
`‖p‖∞ = 1/2` the branch definition of `radial` instead returns `r_J = 3`, and `collarS` is the
junction height `s_J = e^{R₀−r_J} = e^{1/2}`, so both sides agree there too. -/
theorem exp_radial_collar (v : Fin 5) (p y : E2) (hp : 1/2 ≤ nrm p) :
    Real.exp (R0 - radial v p y) = collarS v p y := by
  have hpos : 0 < collarS v p y := by
    rw [collarS, collarHeight]; exact Real.exp_pos _
  by_cases h : nrm p ≤ 1/2
  · -- junction layer: `‖p‖∞ = 1/2`, `radial = r_J` and `collarS = s_J = e^{R₀−r_J}`
    have hpn : nrm p = 1/2 := le_antisymm h hp
    have hrad : radial v p y = rJ := by
      unfold radial; rw [if_pos h, hpn]; norm_num [rJ]
    rw [hrad, collarS, hpn, collarHeight_half]
    unfold R0 rJ sJ
    norm_num
  · -- collar: `radial = R₀ − log (collarS ...)`, so exponentiating inverts `log`
    have hrad : radial v p y = R0 - Real.log (collarS v p y) := by
      unfold radial; rw [if_neg h]
    rw [hrad, show R0 - (R0 - Real.log (collarS v p y)) = Real.log (collarS v p y) by ring]
    exact Real.exp_log hpos

end Work.Cusp
