import Mathlib
import Submission.Work.Escape.Basic
import Submission.Work.Escape.tendsto_norm_iterate_atTop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Escape

/-- The orbit of any point of the escaping region `{z | max 2 ‖c‖ < ‖z‖}` under the mandelbar
iterator `Tantibar c` has norms tending to infinity.  This is the norm-side escape criterion for
the tricorn family, obtained by specialising `tendsto_norm_iterate_atTop` to the `MonicGrowth`
instance `monicGrowth_Tantibar c` (degree `2`, growth constant `‖c‖`). -/
theorem tendsto_norm_Tantibar_iterate_atTop (c z : ℂ) (hz : max 2 ‖c‖ < ‖z‖) :
    Filter.Tendsto (fun n : ℕ => ‖(LeanEval.ComplexAnalysis.Tantibar c)^[n] z‖) Filter.atTop
      Filter.atTop := by
  exact tendsto_norm_iterate_atTop (LeanEval.ComplexAnalysis.Tantibar c) 2 ‖c‖
    (monicGrowth_Tantibar c) le_rfl hz

end Work.Escape
