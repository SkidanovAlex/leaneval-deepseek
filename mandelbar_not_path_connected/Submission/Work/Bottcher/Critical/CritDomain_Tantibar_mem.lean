import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.Green.green_nonneg
import Submission.Work.Bottcher.Green.green_comm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Critical

/-- The critical domain `{G_c > G_c(0)}` is forward invariant under the tricorn map `T_c`.

Indeed `G_c (T_c z) = 2 G_c z` (`green_comm`), while `G_c(0) ≥ 0` (`green_nonneg`); hence
`G_c z > G_c(0)` implies `G_c (T_c z) = 2 G_c z > 2 G_c(0) ≥ G_c(0)`. -/
theorem CritDomain_Tantibar_mem (c z : ℂ) (hz : z ∈ Work.Bottcher.CritDomain c) :
    LeanEval.ComplexAnalysis.Tantibar c z ∈ Work.Bottcher.CritDomain c := by
  rw [Work.Bottcher.mem_CritDomain] at hz ⊢
  rw [Work.Bottcher.Green.green_comm c z]
  have h0 : 0 ≤ Work.Bottcher.greenParam c := by
    rw [Work.Bottcher.greenParam_def]
    exact Work.Bottcher.Green.green_nonneg c 0
  linarith

end Work.Bottcher.Critical
