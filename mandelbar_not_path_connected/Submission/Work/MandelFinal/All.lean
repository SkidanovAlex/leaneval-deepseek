/-
# `Submission/Work/MandelFinal/All.lean` — the whole area

```lean
import Submission.Work.MandelFinal.All
```

* `Submission/Work/MandelFinal/Classical.lean` — `nakaneInput`, `repellingRayParamStable`
  (`gm`), `paramAngleRepelling`, `paramAngleRepelling_quarter`, `parabolicCycleInOmegaLimit`,
  `quarterParabolicIsFixed`: the classical fields of `FinalInputs`, discharged from the delivered
  areas `NAKANE2`/`NAKANE`, `LandLeaves`, `FatouParabolic2`;
* `Submission/Work/MandelFinal/Main.lean` — **`Work.MandelFinal.finalInputs_of`** (the final
  assembly), `Work.MandelFinal.finalInputs_of_landing` (the weaker Landing-level classical
  inputs) and `Work.MandelFinal.mandelbar_not_path_connected_of`;
* `Submission/Work/MandelFinal/Root.lean` — `Work.MandelFinal.rootArcHeightZero_of`: the root-arc
  data `RootArcHeightZero` from the seed `ExplicitRootSeed` and the strong Fatou input;
* `Submission/Work/MandelFinal/seedCert.lean` — `Work.MandelFinal.seedCert`, the certified seed
  `Work.SeedExist.ExplicitRootSeed` (areas `SeedCertNum` + `SeedCertRay`);
* `Submission/Work/MandelFinal/FinalAssembly.lean` — the assembly with the seed substituted:
  `rootArcHeightZero_of_fatou`, `finalInputs_of_fatou`, `mandelbar_not_path_connected_of_fatou`;
* `Submission/Work/MandelFinal/rotationNumberZero_quarter.lean` (+ `MandelFinal/Quarter/`) —
  `Work.MandelFinal.rotationNumberZero_quarter`, the cusp portrait at `1/4` (no hypothesis),
  discharging the last auxiliary input of `Classical.paramAngleRepelling_quarter`;
* `Submission/Work/MandelFinal/Checks.lean` — the axiom audit.
-/
import Submission.Work.MandelFinal.Classical
import Submission.Work.MandelFinal.Main
import Submission.Work.MandelFinal.Root
import Submission.Work.MandelFinal.seedCert
import Submission.Work.MandelFinal.rotationNumberZero_quarter
import Submission.Work.MandelFinal.FinalAssembly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

