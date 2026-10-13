import Mathlib.Tactic.MinImports
import Submission.Work.FTS.StrongPersist.H6Aux.R.SlotsBasic
import Submission.Work.FTS.StrongPersist.H6Aux.R.SlotsBlocks

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.StrongPersist.H6Aux.R.Slots` — the level-one slot infrastructure

Aggregator for the two halves of the infrastructure used by the four slot estimates of the
base case `base_R`: `R.SlotsBasic` (the `wip` manipulation lemmas, the `ℋᵏ`-integrand
integrability, and the integrability-by-domination machinery) and `R.SlotsBlocks` (continuity
of the blocks, the pointwise block bounds against `HkIntegrand`, the `Lhat`-block bounds and
the weighted-square/product integrability workhorses).
-/
