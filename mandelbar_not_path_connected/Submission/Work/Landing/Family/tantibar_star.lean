import Mathlib
import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Family

/-- The tricorn iterator is `star`-conjugate to the family with conjugated parameter:
`T_c(z̄) = conj (T_{c̄} z)`, i.e. `star` intertwines `T_c` and `T_{c̄}`. -/
theorem tantibar_star (c z : ℂ) :
    LeanEval.ComplexAnalysis.Tantibar c (star z) =
      star (LeanEval.ComplexAnalysis.Tantibar (star c) z) := by
  unfold LeanEval.ComplexAnalysis.Tantibar
  simp only [starRingEnd_apply, star_star, star_add, star_pow]

end Work.Landing.Family
