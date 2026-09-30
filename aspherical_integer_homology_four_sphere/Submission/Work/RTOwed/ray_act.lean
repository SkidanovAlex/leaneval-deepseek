import Mathlib
import Submission.Work.RTOwed.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

open Matrix
open scoped Matrix

/-- **The Klein action on the null ray is the diagonal Lorentz action.**  The sign-change action
`Work.FoldInst.act g` of a Klein sign change `g` scales the first four coordinates by the `±1`
vector `Work.FoldInst.signVec g` and leaves the `4`-th ambient coordinate (the "height" `1` of the
null ray) fixed; hence it is multiplication of the null ray by the diagonal matrix
`Work.FoldInst.diagKR (Work.FoldInst.signVec g)`. -/
theorem ray_act (g : Fin 4 → ZMod 2) (y : Work.FoldInst.E4) :
    Work.HypModel.ray (Work.FoldInst.act g y)
      = Matrix.mulVec (Work.FoldInst.diagKR (Work.FoldInst.signVec g)) (Work.HypModel.ray y) := by
  ext i
  fin_cases i <;>
    simp [Work.HypModel.ray, Work.FoldInst.act, Work.HypModel.rot4, Work.FoldInst.diagKR_mulVec,
      Matrix.diagonal_apply]

end Work.RTOwed
