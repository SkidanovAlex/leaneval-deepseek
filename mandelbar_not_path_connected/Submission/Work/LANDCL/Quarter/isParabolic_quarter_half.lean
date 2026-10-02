import Mathlib
import Submission.Work.LANDCL.Defs
import Submission.Work.LANDCL.Deriv.tsq_deriv

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LANDCL.Quarter

/-- The cusp `1/2` of the period-`1` hyperbolic component of the tricorn at `c = 1/4`: the point
`1/2` is fixed by `T̄_{1/4}` and the multiplier of the holomorphic second return map
`Tsq (1/4)` at it is `1`, i.e. `1/2` is a parabolic fixed point of `T̄_{1/4}`. -/
theorem isParabolic_quarter_half : Work.Landing.IsParabolic (1 / 4 : ℂ) 1 (1 / 2 : ℂ) := by
  constructor
  · refine ⟨Nat.one_pos, ?_⟩
    simp only [Function.iterate_one, LeanEval.ComplexAnalysis.Tantibar, starRingEnd_apply]
    norm_num
  · unfold Work.Landing.multiplier2
    rw [Function.iterate_one, Work.LANDCL.Deriv.tsq_deriv]
    norm_num

end Work.LANDCL.Quarter
