import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Escape.Defs
import Submission.Work.Escape.Basic
import Submission.Work.Escape.tendsto_greenIter
import Submission.Work.Bottcher.Core.norm_bottcher_eq_exp_green
import Submission.Work.Bottcher.Critical.CritDomain_escapes
import Submission.Work.Bottcher.Critical.CritDomain_Tantibar_ne_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Core

open Filter Function
open scoped Topology ComplexConjugate

open LeanEval.ComplexAnalysis (Tantibar)
open Work.Bottcher

/-!
# `‖φ_c z‖ = exp (G_c z)` on the critical domain

The general theorem `norm_bottcher_eq_exp_green` proves `‖φ_c z‖ = exp (G_c z)` for any `z`
whose `T_c`-orbit escapes and satisfies the Green-function limit hypothesis; the point of this
file is that both hypotheses are automatic on the critical domain
`CritDomain c = {z | G_c(z) > G_c(0)}`:

* `CritDomain_escapes` gives divergence of `‖T_c^[n] z‖`, and
* the Green function is *defined* as `lim_n 2^{-n} log⁺ ‖T_c^[n] z‖`, so the required limit is
  the defining limit `tendsto_greenIter` (re-indexed from `2^{-n}` to `(1/2)^n`).

Along the way we also need that no iterate of `z` under the holomorphic second iterate `p_c`
hits the critical point `0`: this is `CritDomain_Tantibar_ne_zero` together with
`pMap_iterate c z n : p_c^[n] z = T_c^[2n] z`.
-/

/-- The norm of the Böttcher coordinate on the critical domain is the exponential of the Green
function: `‖φ_c z‖ = exp (G_c z)` for `z ∈ CritDomain c`. -/
theorem norm_bottcher_domain (c z : ℂ) (hz : z ∈ Work.Bottcher.CritDomain c) :
    ‖Work.Bottcher.bottcher c z‖ = Real.exp (Work.Bottcher.green c z) := by
  refine norm_bottcher_eq_exp_green c z ?_ ?_ ?_
  · -- the `T_c`-orbit of `z` escapes to infinity
    exact Work.Bottcher.Critical.CritDomain_escapes c z hz
  · -- the defining limit of the Green function, in the normalisation used by the main theorem
    have hgr := Work.Escape.tendsto_greenIter (Tantibar c) 2 ‖c‖
      (Work.Escape.monicGrowth_Tantibar c) (by norm_num) z
    have hfun : Work.Escape.greenIter (Tantibar c) 2 z
        = fun n : ℕ => ((1 : ℝ) / 2) ^ n * Work.Escape.logPos ‖(Tantibar c)^[n] z‖ := by
      funext n
      rw [Work.Escape.greenIter_def, one_div, inv_pow]
      norm_num
    exact hfun ▸ hgr
  · -- no `p_c`-iterate of `z` hits the critical point
    intro n
    rw [Work.Bottcher.pMap_iterate]
    exact Work.Bottcher.Critical.CritDomain_Tantibar_ne_zero c z hz (2 * n)

end Work.Bottcher.Core
