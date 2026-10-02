import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.Escape.tendsto_norm_iterate_atTop

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The escape dichotomy for the tricorn

For the antiholomorphic unicritical family `T_c(z) = z̄² + c` the norm of the orbit of a point `z`
either stays bounded for all time, or escapes to infinity.  Concretely this file proves

`bounded_or_escapes : (∃ M, ∀ n, ‖T_c^[n] z‖ ≤ M) ∨ ‖T_c^[n] z‖ → ∞`.

The proof is the standard escape dichotomy for a degree-`2` monic-growth map: `T_c` satisfies
`Work.Escape.MonicGrowth (Tantibar c) 2 ‖c‖`, and once the orbit crosses the escape radius
`max 2 ‖c‖ = Work.Escape.escapeRegion ‖c‖` its norms grow without bound
(`Work.Escape.tendsto_norm_iterate_atTop`).  Hence an orbit which is unbounded (so that some
iterate crosses the escape radius) escapes, while an orbit which never crosses the escape radius
is bounded.
-/

open Filter Function
open scoped Topology

namespace Work.Bottcher.Green

/-- **Escape dichotomy.** For the tricorn family `T_c(z) = z̄² + c` the orbit of any point `z`
either has bounded norms, or its norms tend to `+∞`. -/
theorem bounded_or_escapes (c z : ℂ) :
    (∃ M : ℝ, ∀ n : ℕ, ‖(LeanEval.ComplexAnalysis.Tantibar c)^[n] z‖ ≤ M) ∨
      Filter.Tendsto (fun n : ℕ => ‖(LeanEval.ComplexAnalysis.Tantibar c)^[n] z‖)
        Filter.atTop Filter.atTop := by
  by_cases hb : ∃ M : ℝ, ∀ n : ℕ, ‖(LeanEval.ComplexAnalysis.Tantibar c)^[n] z‖ ≤ M
  · exact Or.inl hb
  · right
    -- The orbit is unbounded, so some iterate crosses the escape radius `max 2 ‖c‖`.
    push Not at hb
    obtain ⟨N, hN⟩ := hb (max 2 ‖c‖)
    -- From there on the norms grow without bound, hence so does the whole sequence.
    have hesc := Work.Escape.tendsto_norm_iterate_atTop (LeanEval.ComplexAnalysis.Tantibar c) 2 ‖c‖
      (Work.Escape.monicGrowth_Tantibar c) (by norm_num)
      (z := (LeanEval.ComplexAnalysis.Tantibar c)^[N] z) hN
    rw [← tendsto_add_atTop_iff_nat N]
    simpa only [Function.iterate_add_apply] using hesc

end Work.Bottcher.Green
