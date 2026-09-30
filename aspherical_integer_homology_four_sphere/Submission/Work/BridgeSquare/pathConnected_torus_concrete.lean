import Mathlib
import Submission.Work.RTOwed.FinalInstance

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.BridgeSquare

/-- **The torus factor of the concrete instance is path connected.**

`Work.RTOwed.rtData` is built from `Work.RTInstance.assemblyOf`, whose torus factor is the concrete
`Work.RTInstance.Torus = (ℝ/ℤ)² = Fin 2 → AddCircle 1`; that is *definitionally* the type appearing
in the statement, and `PathConnectedSpace` holds there because `ℝ/ℤ` is a quotient of `ℝ`
(`AddCircle.pathConnectedSpace`) and a product of path connected spaces is path connected. -/
theorem pathConnected_torus_concrete (v : Work.Space.Cusp) :
    PathConnectedSpace ((Work.RTOwed.rtData).core.Torus v) := by
  show PathConnectedSpace (Fin 2 → AddCircle (1 : ℝ))
  infer_instance

end Work.BridgeSquare
