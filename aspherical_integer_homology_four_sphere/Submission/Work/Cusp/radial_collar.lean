import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The radial coordinate of the collar is `R₀ − log s`

`radial v p y` is the metric radial coordinate of the filling of the `v`-th cusp: in the inner
region `‖p‖∞ ≤ 1/2` it is `2 r_J ‖p‖∞`, and in the collar `‖p‖∞ ≥ 1/2` it is `R₀ − log s`, where
`s = collarS v p y` is the UHS height of the outer chart `Θ_v`.

The two branches agree on the whole collar `‖p‖∞ ≥ 1/2`:

* for `‖p‖∞ > 1/2` the definition *is* the claimed right hand side, and
* at the junction `‖p‖∞ = 1/2` both sides equal `r_J = 3`: the left hand side is
  `2 r_J · (1/2) = r_J`, while the collar height at `t = 1/2` is `collarHeight (1/2) b = s_J`
  independently of the ceiling `b`, so the right hand side is `R₀ − log s_J = 7/2 − 1/2 = 3`.

This is the definitional identity used to make the collar branch of `radial` computable.
-/

namespace Work.Cusp

/-- **The collar identity for the radial coordinate.** For every point of the collar
(`1/2 ≤ ‖p‖∞`) the metric radial coordinate `radial v p y` is the UHS value `R₀ − log (collarS v p y)`
of the outer chart. -/
theorem radial_collar (v : Fin 5) (p y : E2) (hp : 1/2 ≤ nrm p) :
    radial v p y = R0 - Real.log (collarS v p y) := by
  rw [radial]
  split_ifs with h
  · -- junction layer `‖p‖∞ = 1/2`: the collar height collapses to the junction height `s_J`
    have hnp : nrm p = 1/2 := le_antisymm h hp
    have hsJ : 0 < sJ := by rw [sJ]; exact Real.exp_pos _
    have hcol : collarS v p y = sJ := by
      rw [collarS, hnp, collarHeight]
      norm_num
      exact Real.exp_log hsJ
    rw [hcol, hnp]
    unfold R0 rJ sJ
    rw [Real.log_exp]
    norm_num
  · -- interior of the collar: this is the defining branch of `radial`
    rfl

end Work.Cusp
