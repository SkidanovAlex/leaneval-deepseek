import Mathlib
import Submission.Work.LANDCL.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LANDCL.Deriv

/-- **The critical preimage equation of the mandelbar iterator**: `T̄_c` is antiholomorphic of
order two, so the equation `T̄_c z = 0` is equivalent to the (conjugated) holomorphic equation
`z ^ 2 = -star c`.  In particular the unique preimage of the critical value `0` is the critical
point `z = 0` (at `c = 0`), the fact used by `Work.LANDCL.not_isRepelling_criticalValue`. -/
theorem preimage_zero (c z : ℂ) :
    LeanEval.ComplexAnalysis.Tantibar c z = 0 ↔ z ^ 2 = -star c := by
  have hT : star (LeanEval.ComplexAnalysis.Tantibar c z) = z ^ 2 + star c := by
    rw [LeanEval.ComplexAnalysis.Tantibar]
    simp
  rw [← star_eq_zero, hT, eq_neg_iff_add_eq_zero]

end Work.LANDCL.Deriv
