import Mathlib
import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Family

open LeanEval.ComplexAnalysis (Tantibar)

/-- The antiholomorphic quadratic `T̄_c(z) = z̄² + c` is continuous: it is a sum of a square of
a continuous (conjugation) map and a constant. -/
theorem tantibar_continuous (c : ℂ) : Continuous (LeanEval.ComplexAnalysis.Tantibar c) := by
  unfold LeanEval.ComplexAnalysis.Tantibar
  fun_prop

end Work.Landing.Family
