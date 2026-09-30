import Mathlib
import Submission.Work.Cusp.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Cusp

/-- The slope `σ_v = κ_{v,1} + b_v κ_{v,2} + c_v κ_{v,3}` is a nonzero vector of `ℝ³`: in cube
coordinates its third coordinate is `-2 b_v ≠ 0` (for `v ≤ 3` it is `-210`, for `v = 4` it is
`-212`), because `κ_{v,1}` and `κ_{v,3}` both have zero third coordinate.  Nonvanishing is what
makes `σ_v` a genuine meridian direction and `(frame1 v, frame2 v, frame3 v)` a well-defined
orthonormal frame. -/
theorem slope_ne_zero (v : Fin 5) : slope v ≠ 0 := by
  intro h
  have h2 : slope v 2 = 0 := by
    rw [h]; simp
  fin_cases v <;>
    simp [slope, kv, kappa, slopeB, slopeC] at h2

end Work.Cusp
