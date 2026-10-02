import Mathlib
import Submission.Work.FatouParabolic.Defs
import Submission.Work.LANDCL.Critical.not_isRepelling_criticalValue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Iterates of `Tsq c` at a preimage of the critical point of `T_c`

Let `T_c(z) = z̄² + c` be the antiholomorphic quadratic and let `Tsq c = (T_c)^[2]` be its
holomorphic second iterate, `Tsq c z = (z² + c̄)² + c`.  In this file we record the elementary
fact that a preimage `u` of the critical point `0` of `T_c` (that is, `T_c u = 0`) has
`Tsq`-orbit starting at the critical value: `Tsq c u = T_c(T_c u) = T_c 0 = c`.

Concretely, for every `n`,

`(Tsq c)^[n+1] u = (T_c)^[2n+1] 0`,

the left-hand side being `(T_c)^[2n+2] u = (T_c)^[2n+1] (T_c u) = (T_c)^[2n+1] 0`.  In
particular the value of the iterate is independent of *which* preimage `u` of `0` is chosen:
all of them land on the critical value `c = T_c 0` after one application of `Tsq c` and then
follow the critical orbit.

This is used in `Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff`, where the
critical points of the iterates of `Tsq c` are located.
-/

namespace Work.FatouParabolic.Critical

/-- `Tsq c` is the second iterate of the antiholomorphic quadratic `T_c(z) = z̄² + c`:
`Tsq c z = T_c (T_c z) = (z² + c̄)² + c`. -/
theorem tsq_eq_Tantibar_iterate_two (c : ℂ) :
    Work.Landing.Tsq c = (LeanEval.ComplexAnalysis.Tantibar c)^[2] := by
  funext z
  simp [Work.Landing.Tsq, LeanEval.ComplexAnalysis.Tantibar, Function.iterate_succ]

/-- **A preimage `u` of the critical point `0` of `T_c` reaches the critical orbit after one
`Tsq`-step**: `(Tsq c)^[n+1] u = (T_c)^[2n+1] 0`.

Indeed `T_c u = 0`, so `Tsq c u = T_c (T_c u) = T_c 0 = c`, and
`(Tsq c)^[n] = (T_c)^[2n]` (`tsq_eq_Tantibar_iterate_two`). -/
theorem tsq_iterate_of_Tantibar_eq_zero {c u : ℂ} (hu : LeanEval.ComplexAnalysis.Tantibar c u = 0) (n : ℕ) :
    (Work.Landing.Tsq c)^[n + 1] u = (LeanEval.ComplexAnalysis.Tantibar c)^[2 * n + 1] 0 := by
  calc (Work.Landing.Tsq c)^[n + 1] u
      = (LeanEval.ComplexAnalysis.Tantibar c)^[2 * (n + 1)] u := by
        rw [tsq_eq_Tantibar_iterate_two, ← Function.iterate_mul]
    _ = (LeanEval.ComplexAnalysis.Tantibar c)^[2 * n + 1 + 1] u := by
        rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
    _ = (LeanEval.ComplexAnalysis.Tantibar c)^[2 * n + 1]
          (LeanEval.ComplexAnalysis.Tantibar c u) :=
        Function.iterate_succ_apply (LeanEval.ComplexAnalysis.Tantibar c) (2 * n + 1) u
    _ = (LeanEval.ComplexAnalysis.Tantibar c)^[2 * n + 1] 0 := by rw [hu]

end Work.FatouParabolic.Critical
