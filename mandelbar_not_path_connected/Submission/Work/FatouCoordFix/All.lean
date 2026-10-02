/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoordFix team
-/
import Submission.Work.FatouCoordFix.Defs
import Submission.Work.FatouCoordFix.PgFlower
import Submission.Work.FatouCoordFix.HPetal.HPlanePetal_isOpen
import Submission.Work.FatouCoordFix.HPetal.HPlanePetal_preconnected
import Submission.Work.FatouCoordFix.HPetal.HPlanePetal_nonempty
import Submission.Work.FatouCoordFix.HPetal.HPlanePetal_mul_norm_lt
import Submission.Work.FatouCoordFix.HPetal.HPlanePetal_subset_WidePetal
import Submission.Work.FatouCoordFix.HPetal.HPlanePetal_mapsTo_wMap
import Submission.Work.FatouCoordFix.HPetal.HPlanePetal_mapsTo_gChart
import Submission.Work.FatouCoordFix.HPetal.exists_iterate_mem_HPlanePetal
import Submission.Work.FatouCoordFix.HPetal.Petal_subset_WidePetal
import Submission.Work.FatouCoordFix.FlowerFix.gChart_re_growth
import Submission.Work.FatouCoordFix.FlowerFix.measurable_indicator_of_differentiableOn
import Submission.Work.FatouCoordFix.FlowerFix.GermFix
import Submission.Work.FatouCoordFix.FlowerFix.TransferFix
import Submission.Work.FatouCoordFix.FlowerFix.ExistsFix
import Submission.Work.FatouCoordFix.Repelling.ZCorrection
import Submission.Work.FatouCoordFix.Repelling.Z_Omega_decay
import Submission.Work.FatouCoordFix.Repelling.ZDecay

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Submission/Work/FatouCoordFix/` — the repaired Leau–Fatou flower interface

Umbrella module: imports the whole area.

* `Work.FatouCoordFix.ParabolicFlowerFix` (in `Defs`) — the delivered `ParabolicFlower` plus a
  `g`-invariant half-plane sub-petal `Pg ⊆ Pa` and the Abel equation `φa ∘ F = φa + 1` on `Pa`.
* `Work.FatouCoordFix.FlowerFix.exists_parabolicFlowerFix` / `..._small` — existence, with the
  petal and the half-petal as small as we like.
* `Work.FatouCoordFix.HalfPetalFlower` (in `PgFlower`) — the flower restated on `Pg`.
* `Work.FatouCoordFix.Repelling.exists_conjugacy_Z` / `Z_tendsto_zero` / `V_sub_tendsto` — the
  repelling conjugacy `V w = w + (1-a) Λ w + Z w` with the fixed-point form and the decay of `Z`.
-/
