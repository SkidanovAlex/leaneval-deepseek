import Mathlib
import Submission.Work.SeedFatou.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The critical points of the second return map are in the grand orbit of `0`

`F c = (T_c)^[10] = (Tsq c)^[5]` with `Tsq c z = (z² + c̄)² + c = (T_c)^[2] z`.  By the chain
rule the derivative of `(Tsq c)^[5]` at `w` is the product of the derivatives of `Tsq c` along
the orbit `w, (Tsq c) w, …, (Tsq c)^[4] w`, and `deriv (Tsq c) z = 4·z·(z² + c̄)` vanishes
exactly at the critical point `0` and at the preimages of `0` under `T_c`
(`Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff`).  Hence if `w` is critical for
`F c`, some `(Tsq c)^[j] w`, `j < 5`, is `0` or a `T_c`-preimage of `0`; reading
`(Tsq c)^[j] = (T_c)^[2j]` gives `(T_c)^[k] w = 0` for `k = 2j` or `k = 2j+1`, and
`k ≤ 9 < 10`.
-/

namespace Work.SeedFatou

open LeanEval.ComplexAnalysis (Tantibar)

theorem exists_tantibar_iterate_eq_zero {c w : ℂ} (h : deriv (Work.FSeed.F c) w = 0) :
    ∃ k : ℕ, k < 10 ∧ (LeanEval.ComplexAnalysis.Tantibar c)^[k] w = 0 := by
  have h5 : deriv ((Work.Landing.Tsq c)^[5]) w = 0 := h
  rcases (Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff c (m := 5)).mp h5
    with ⟨j, hj, hcase⟩
  rw [Finset.mem_range] at hj
  -- `(Tsq c)^[j] = (T_c)^[2 * j]`
  have hTj : (Tantibar c)^[2 * j] w = (Work.Landing.Tsq c)^[j] w := by
    rw [Function.iterate_mul, Work.FSeed.Tantibar_iterate_two]
  rcases hcase with hz | hz
  · -- `(Tsq c)^[j] w = 0`, take `k = 2j`
    exact ⟨2 * j, by omega, by rw [hTj, hz]⟩
  · -- `T_c ((Tsq c)^[j] w) = 0`, take `k = 2j+1`
    refine ⟨2 * j + 1, by omega, ?_⟩
    have hstep : (Tantibar c)^[2 * j + 1] w = Tantibar c ((Tantibar c)^[2 * j] w) := by
      rw [show 2 * j + 1 = 1 + 2 * j from by omega, Function.iterate_add_apply,
        Function.iterate_one]
    rw [hstep, hTj, hz]

end Work.SeedFatou
