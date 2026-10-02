/-
# The Böttcher equation for `p_c = T_c ∘ T_c` on the critical domain

The product formula satisfies `φ_c (p_c z) = φ_c(z)^4` on all of `CritDomain c`
(`{G_c > G_c(0)}`); this is the domain-restricted form of
`Work.Bottcher.Core.bottcher_comm_pMap`.  Unlike the Böttcher equation for `T_c`
itself, this statement has *no* branch defect: it holds on the whole escape set
(and in particular on `CritDomain c`).
-/
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Core.bottcher_comm_pMap
import Submission.Work.Bottcher.Critical.CritDomain_escapes
import Submission.Work.Bottcher.Critical.CritDomain_Tantibar_ne_zero

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Function
open scoped Topology

namespace Work.Bottcher.Core

open LeanEval.ComplexAnalysis (Tantibar)

theorem bottcher_comm_pMap_domain (c z : ℂ) (hz : z ∈ Work.Bottcher.CritDomain c) :
    Work.Bottcher.bottcher c (Work.Bottcher.pMap c z) = (Work.Bottcher.bottcher c z) ^ 4 := by
  refine bottcher_comm_pMap c z (Critical.CritDomain_escapes c z hz) fun n => ?_
  have h := Critical.CritDomain_Tantibar_ne_zero c z hz (2 * n)
  rwa [← pMap_iterate c z n] at h

end Work.Bottcher.Core
