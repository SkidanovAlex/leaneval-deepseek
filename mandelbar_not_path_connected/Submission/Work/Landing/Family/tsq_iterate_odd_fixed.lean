import Mathlib
import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Family

/-- `Tsq c` is the second iterate of the antiholomorphic quadratic `Tantibar c`:
`(Tantibar c)^[2] z = (z² + c̄)² + c = Tsq c z`. -/
lemma tsq_eq_Tantibar_iterate_two (c : ℂ) :
    Work.Landing.Tsq c = (LeanEval.ComplexAnalysis.Tantibar c)^[2] := by
  funext z
  simp [Work.Landing.Tsq, LeanEval.ComplexAnalysis.Tantibar, Function.iterate_succ, map_add,
    map_pow]

set_option linter.unusedVariables false in
/-- A point fixed by the `k`-th iterate of `Tantibar c` is fixed by the `k`-th iterate of the
holomorphic second return map `Tsq c = (Tantibar c)^[2]`.  (The oddness of `k` is not needed
for this inclusion; it is part of the ambient setting of the landing theorem.) -/
theorem tsq_iterate_odd_fixed (c : ℂ) {k : ℕ} (hk : Odd k) {x : ℂ}
    (hx : (LeanEval.ComplexAnalysis.Tantibar c)^[k] x = x) :
    (Work.Landing.Tsq c)^[k] x = x := by
  have hTsq := tsq_eq_Tantibar_iterate_two c
  rw [hTsq, ← Function.iterate_mul, two_mul, Function.iterate_add_apply, hx, hx]

end Work.Landing.Family
