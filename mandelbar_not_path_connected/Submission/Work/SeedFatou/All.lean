/-
# `Submission/Work/SeedFatou/` — Fatou's strong form at the seed, and the root

Import this module to get the whole area.

## Main results

* `Work.SeedFatou.fatouCritInBasin (S : Work.SeedExist.RootSeedData) :
    Work.SeedExist.FatouCritInBasin S.c S.z₁ (Work.SeedExist.flowerOf S).Pg`
  — Fatou's theorem in the strong (immediate-basin) form, at **every** `RootSeedData`, with no
  hypothesis.  It supplies the `crit` and `wake` fields of `Work.EL.RootParabolic` through
  `Work.SeedExist.rootParabolicEL_of_seedData`.
* `Work.SeedFatou.rootArcHeightZero : Work.FinalFix.RootArcHeightZero`
  — the `root` argument of `Work.MandelFinal.finalInputs_of`, with no hypothesis.

## Supporting lemmas (all `Work.SeedFatou`)

* `basin_subset_K`, `image_interior_K_subset` — the immediate basin lies in the filled Julia set,
  and the interior of the filled Julia set is `T_c`-invariant;
* `exists_tantibar_iterate_eq_zero` — a critical point of `F c = (T_c)^[10]` reaches `0` within
  `9` `T_c`-steps;
* `CritImmData`, `exists_critImm` — the packaged immediate-basin datum of the seed;
* `fatouCrit_clause_i`, `fatouCrit_clause_ii` — the two clauses of `FatouCritInBasin`.

## Non-results

Nothing here uses `sorry`, a new axiom or `native_decide`; no numerics are needed, this is not a
certificate area.
-/
import Submission.Work.SeedFatou.Defs
import Submission.Work.SeedFatou.basin_subset_K
import Submission.Work.SeedFatou.image_interior_K_subset
import Submission.Work.SeedFatou.exists_tantibar_iterate_eq_zero
import Submission.Work.SeedFatou.exists_critImm
import Submission.Work.SeedFatou.fatouCrit_clause_i
import Submission.Work.SeedFatou.fatouCrit_clause_ii
import Submission.Work.SeedFatou.FatouCritInBasin
import Submission.Work.SeedFatou.RootArcHeightZero
import Submission.Work.SeedFatou.Wire

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

