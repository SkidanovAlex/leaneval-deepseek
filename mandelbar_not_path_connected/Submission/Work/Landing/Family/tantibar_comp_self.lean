import Mathlib
import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Family

/-- The holomorphic second iterate `Tsq c` of `Core` really is the composite `T_c ∘ T_c` of the
antiholomorphic quadratic `T_c(z) = z̄² + c` with itself:  for every `z`,
`T_c(T_c z) = (z² + c̄)² + c`. -/
theorem tantibar_comp_self (c : ℂ) :
    LeanEval.ComplexAnalysis.Tantibar c ∘ LeanEval.ComplexAnalysis.Tantibar c =
      Work.Landing.Tsq c := by
  funext z
  simp only [Function.comp_apply, LeanEval.ComplexAnalysis.Tantibar, Work.Landing.Tsq,
    starRingEnd_apply, star_add, star_pow, star_star]

end Work.Landing.Family
