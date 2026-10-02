import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Green.green_nonneg
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.Bottcher.Critical.CritDomain_Tantibar_mem

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Forward invariance of the critical domain under the second iterate `p_c`

`CritDomain c = {z : G_c(z) > G_c(0)}` is forward invariant under the tricorn map
`T_c` (`CritDomain_Tantibar_mem`).  Since the holomorphic second iterate `p_c` is
`T_c^[2]` (`Work.Bottcher.pMap_eq_iterate_two`), applying the one-step invariance
twice gives that `CritDomain c` is forward invariant under `p_c` as well.
-/

namespace Work.Bottcher.Critical

open LeanEval.ComplexAnalysis (Tantibar)

/-- The critical domain `{G_c > G_c(0)}` is forward invariant under the holomorphic
second iterate `p_c = T_c ∘ T_c`. -/
theorem CritDomain_pMap_mem (c z : ℂ) (hz : z ∈ Work.Bottcher.CritDomain c) :
    Work.Bottcher.pMap c z ∈ Work.Bottcher.CritDomain c := by
  rw [Work.Bottcher.pMap_eq_iterate_two]
  rw [show (Tantibar c)^[2] z = Tantibar c (Tantibar c z) by
      rw [Function.iterate_succ_apply']; simp]
  exact CritDomain_Tantibar_mem c (Tantibar c z) (CritDomain_Tantibar_mem c z hz)

end Work.Bottcher.Critical
