import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.Escape.Basic
import Submission.Work.Escape.tendsto_greenIter

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Green function of the tricorn is nonnegative

`Work.Bottcher.green c z` is the Green function `G_c(z)` of the tricorn map
`T_c(w) = w̄^2 + c`, defined as `limUnder atTop` of the partial Green functions
`greenIter (T_c) 2 z n = 2^{-n} log⁺ ‖T_c^[n] z‖`.

Each partial Green function is nonnegative, since `log⁺ ≥ 0` and `2^{-n} > 0`
(`Work.Escape.greenIter_nonneg`).  Moreover the partial Green functions genuinely
converge to `G_c(z)` (`Work.Escape.tendsto_greenIter`, applicable to every `c` and `z`
because `T_c` has `MonicGrowth` of degree `2` with constant `‖c‖`).  Hence `G_c(z)` is
the limit of a sequence of nonnegative reals, so `0 ≤ G_c(z)`.
-/

open Filter Function
open scoped Topology

namespace Work.Bottcher.Green

open LeanEval.ComplexAnalysis (Tantibar)

/-- Every partial Green function of the tricorn map is nonnegative. -/
theorem greenIter_Tantibar_nonneg (c z : ℂ) (n : ℕ) :
    0 ≤ Work.Escape.greenIter (Tantibar c) 2 z n :=
  Work.Escape.greenIter_nonneg (Tantibar c) 2 z n

/-- The partial Green functions of the tricorn map converge to the Green function, for every
parameter `c` and every point `z` (no hypothesis on `c` or `z` is needed, since `T_c` always has
degree-`2` monic growth with constant `‖c‖`). -/
theorem tendsto_greenIter_Tantibar (c z : ℂ) :
    Filter.Tendsto (Work.Escape.greenIter (Tantibar c) 2 z) Filter.atTop
      (nhds (Work.Bottcher.green c z)) :=
  Work.Escape.tendsto_greenIter (Tantibar c) 2 ‖c‖ (Work.Escape.monicGrowth_Tantibar c) le_rfl z

theorem green_nonneg (c z : ℂ) : 0 ≤ Work.Bottcher.green c z :=
  ge_of_tendsto' (tendsto_greenIter_Tantibar c z) (greenIter_Tantibar_nonneg c z)

end Work.Bottcher.Green
