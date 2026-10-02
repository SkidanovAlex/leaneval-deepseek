/-
Copyright: subproject `Submission/Work/FatouParabolic/` of `mandelbar_not_path_connected`.

# `Submission/Work/FatouParabolic/` — Fatou's theorem on parabolic cycles (one-stop import)

See `Submission/Work/FatouParabolic/NOTES.md` for the map of the area, the conventions and the
main results.

The entry points of the area are

* `Work.FatouParabolic.FatouParabolicInput` — the primitive classical input (Fatou's theorem on
  parabolic cycles);
* `Work.FatouParabolic.parabolicCycleInOmegaLimit` — `Work.LANDCL.ParabolicCycleInOmegaLimit c`
  for every `c`, from the input;
* `Work.FatouParabolic.quarterParabolicIsFixed` (and the finer
  `...quarterParabolicIsFixed_of`) — `Work.LANDCL.QuarterParabolicIsFixed` from the input;
* `Work.FatouParabolic.Quarter.tendsto_quarter_criticalOrbit` — the unconditional real dynamics
  `(T_{1/4})^[n] (1/4) → 1/2`;
* `Work.FatouParabolic.exists_isCriticalPoint_in_basin_of_polynomialMap` — the petal/Liouville
  core of the primitive input (`Core/Main.lean`).

This module imports the seed export too, which pulls in `Submission.Work.FQC.Petal`; a caller
that does not need it can import the individual modules instead.
-/
import Submission.Work.FatouParabolic.Defs
import Submission.Work.FatouParabolic.Basin.mapsTo_puncturedBasin
import Submission.Work.FatouParabolic.Basin.preimage_mem_puncturedBasin
import Submission.Work.FatouParabolic.Critical.deriv_iterate_tsq_eq_zero_iff
import Submission.Work.FatouParabolic.Critical.multiplier2_zero_ne_one
import Submission.Work.FatouParabolic.Critical.tsq_iterate_of_Tantibar_eq_zero
import Submission.Work.FatouParabolic.Poly.tsq_iterate_isPolynomialMap
import Submission.Work.FatouParabolic.Poly.isPolynomialMap_surjective
import Submission.Work.FatouParabolic.Poly.isPolynomialMap_basinEscape
import Submission.Work.FatouParabolic.Poly.isPolynomialMap_differentiable
import Submission.Work.FatouParabolic.Reduction
import Submission.Work.FatouParabolic.Quarter
import Submission.Work.FatouParabolic.Quarter.tendsto_quarter_criticalOrbit
import Submission.Work.FatouParabolic.Core.Defs
import Submission.Work.FatouParabolic.Core.isOpen_puncturedBasin
import Submission.Work.FatouParabolic.Core.isBounded_puncturedBasin_of_escape
import Submission.Work.FatouParabolic.Core.extFatou_independent
import Submission.Work.FatouParabolic.Core.extFatou_abel
import Submission.Work.FatouParabolic.Core.extFatou_differentiableOn
import Submission.Work.FatouParabolic.Core.extFatou_injective_of_injOn
import Submission.Work.FatouParabolic.Core.extFatou_surjective_of_imageStrip
import Submission.Work.FatouParabolic.Core.false_of_bounded_of_injOn_of_surjective
import Submission.Work.FatouParabolic.Core.isLocalHomeomorphOn_of_deriv_ne_zero
import Submission.Work.FatouParabolic.Core.finite_fiber_of_isLocalHomeomorphOn
import Submission.Work.FatouParabolic.Core.isProperMap_of_escapeBound
import Submission.Work.FatouParabolic.Core.injOn_of_simplyConnected_of_noCriticalPoint
import Submission.Work.FatouParabolic.Core.exists_flowerImageFix
import Submission.Work.FatouParabolic.Core.exists_criticalPoint_in_basin_of_rootParabolic
import Submission.Work.FatouParabolic.Core.exists_criticalPoint_in_basin_of_rootParabolic_of_crit
import Submission.Work.FatouParabolic.Core.false_of_bounded_of_holomorphic_bijection
import Submission.Work.FatouParabolic.Core.pdExtFatou_independent
import Submission.Work.FatouParabolic.Core.ImmBasin.Defs
import Submission.Work.FatouParabolic.Core.immBasin_basics_interior
import Submission.Work.FatouParabolic.Core.ImmBasin.LiftTools
import Submission.Work.FatouParabolic.Core.ImmBasin.exists_differentiable_strip_lift
import Submission.Work.FatouParabolic.Core.ImmBasin.false_of_petalInverse_of_covering
import Submission.Work.FatouParabolic.Core.isCoveringMap_iterate_immBasin
import Submission.Work.FatouParabolic.Core.exists_petalInverse
import Submission.Work.FatouParabolic.Core.exists_strip_lift
import Submission.Work.FatouParabolic.Core.exists_isCriticalPoint_in_immBasin
import Submission.Work.FatouParabolic.Core.Main
import Submission.Work.FatouParabolic.SeedExport

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

