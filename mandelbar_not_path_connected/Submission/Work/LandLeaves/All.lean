/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

Aggregator of the area.  Import `Submission.Work.LandLeaves.All` for the landing leaf inputs of
ledger §5 that this area owns.

| ledger item | main export |
|---|---|
| 1 (angle defect of `RotationNumberZero`) | repair of `Work.Landing.RotationNumberZero` + `Work.LandLeaves.rotationNumberZero_iff_Ico` + the refutation `Work.LandLeaves.not_rotationNumberZero_raw` (done) |
| 2 `DynBottcherOnlyOnMandelbar` | **proved**: `Work.LandLeaves.dynBottcherOnlyOnMandelbar`, `dynBottcherExists_iff_mem_mandelbar`, `mem_mandelbar_of_landsAt`, `repellingRayParamStable_of_goldbergMilnor` |
| 3 `AttractingCyclesInner` | **proved**: `Work.LandLeaves.attractingCyclesInner` |
| 4 `PeriodicRaysLand` / LANDCL reductions | **proved**: `Work.LandLeaves.periodicRaysLand`, the accumulation-set form `RayAccumSingleton`, the structural lemmas (`rayAccum_nonempty`, `isCompact_rayAccum`, `rayAccum_iterate_image`, `isPreconnected_rayAccum`, `rayAccum_subset_fixp`) and the assembled rows `Work.LandLeaves.paramAngleRepelling_of_rootArc_landed` etc. (`Rows.lean`) |
| 5 `SnailDichotomy` | chain **proved** except the germ lemma: `SnailLemmaMilnor → NoNeutralLanding → SnailDichotomy` (`noNeutralLanding.lean`, `snailDichotomy_of_noNeutral.lean`), plus the odd-period and real-multiplier cases; the germ lemma `LandLeaves/snailLemmaMilnor` is the single remaining classical input |
| 6 `GoldbergMilnorB1` | delegated (`LandLeaves/goldbergMilnorB1`) |
-/
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.Reductions
import Submission.Work.LandLeaves.dynBottcherOnlyOnMandelbar
import Submission.Work.LandLeaves.attractingCyclesInner
import Submission.Work.LandLeaves.repelling_or_parabolic_of_multiplier_real
import Submission.Work.LandLeaves.SnailLemma
import Submission.Work.LandLeaves.SnailLemmaMilnor
import Submission.Work.LandLeaves.snailDichotomy_of_noNeutral
import Submission.Work.LandLeaves.snailLemma
import Submission.Work.LandLeaves.noNeutralLanding
import Submission.Work.LandLeaves.noNeutralLanding_of_snailMilnor
import Submission.Work.LandLeaves.rayAccum_nonempty
import Submission.Work.LandLeaves.isCompact_rayAccum
import Submission.Work.LandLeaves.rayAccum_periodic
import Submission.Work.LandLeaves.periodicRaysLand
import Submission.Work.LandLeaves.Rows
import Submission.Work.LandLeaves.Final
import Submission.Work.LandLeaves.snailLemmaMilnor
import Submission.Work.LandLeaves.goldbergMilnorB1
import Submission.Work.LandLeaves.SnailPathDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

