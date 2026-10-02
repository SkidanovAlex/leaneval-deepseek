import Submission.Work.Landing.Angle.angDoubleQ_iterate
import Submission.Work.Landing.Angle.angDouble_coe_rat
import Submission.Work.Landing.Angle.angDouble_coe_rat_iterate
import Submission.Work.Landing.Angle.angDouble_fract
import Submission.Work.Landing.Angle.angDouble_iterate_succ
import Submission.Work.Landing.Angle.angleOrbit_paramAngle
import Submission.Work.Landing.Angle.angleOrbit_rootAngle
import Submission.Work.Landing.Angle.exactPeriodAngle_paramAngle
import Submission.Work.Landing.Angle.exactPeriodAngle_rootAngle1
import Submission.Work.Landing.Angle.exactPeriodAngle_rootAngle2
import Submission.Work.Landing.Angle.firstReturn_rootAngles
import Submission.Work.Landing.Angle.periodicAngle_add_mul
import Submission.Work.Landing.Angle.rootOrbit_pairs
import Submission.Work.Landing.Angle.wakeArc_endpoints
import Submission.Work.Landing.Angle.wakeArc_step
import Submission.Work.Landing.Angle.wakeArc_width
import Submission.Work.Landing.Angle.window_separation
import Submission.Work.Landing.Angles
import Submission.Work.Landing.Caratheodory.landsAt_of_extension
import Submission.Work.Landing.Core
import Submission.Work.Landing.Family.deriv_tsq
import Submission.Work.Landing.Family.deriv_tsq_iterate_odd_real
import Submission.Work.Landing.Family.deriv_tsq_iterate_star
import Submission.Work.Landing.Family.iterate_one_eq_of_iterate_eq
import Submission.Work.Landing.Family.tantibar_comp_self
import Submission.Work.Landing.Family.tantibar_contDiff
import Submission.Work.Landing.Family.tantibar_continuous
import Submission.Work.Landing.Family.tantibar_iterate_star
import Submission.Work.Landing.Family.tantibar_iterate_two_mul
import Submission.Work.Landing.Family.tantibar_iterate_two_mul_add_one
import Submission.Work.Landing.Family.tantibar_star
import Submission.Work.Landing.Family.tsq_iterate_odd_comp
import Submission.Work.Landing.Family.tsq_iterate_odd_fixed
import Submission.Work.Landing.Family.tsq_iterate_star
import Submission.Work.Landing.Family.tsq_star
import Submission.Work.Landing.Land
import Submission.Work.Landing.Land.Caratheodory
import Submission.Work.Landing.Land.Landing
import Submission.Work.Landing.Land.Main
import Submission.Work.Landing.Rays
import Submission.Work.Landing.Rays.dynRay_sublevel_infinite
import Submission.Work.Landing.Rays.image_dynRay_subset
import Submission.Work.Landing.Rays.image_rayAccum
import Submission.Work.Landing.Rays.isBounded_dynRay_sublevel
import Submission.Work.Landing.Rays.preimage_mem_dynRay
import Submission.Work.Landing.Rays.radialRay_norm
import Submission.Work.Landing.Rays.rayAccum_image_homeo
import Submission.Work.Landing.Rays.rayAccum_iterate_homeo
import Submission.Work.Landing.Rays.rayDirection_eq_of_sub_int

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.Landing` — landing of periodic rays of the tricorn

The landing area of the `mandelbar_not_path_connected` project: dynamic rays, the ray transfer
under `T_c`, the landing theorem (Milnor 18.10, existence + classification) and the angle
combinatorics of the root rays `371/1023`, `404/1023`, of the window angle `23/63` and of the
lifted L-wake arcs `W_j`.

Import this module to get the whole area; see `Submission/Work/Landing/NOTES.md` for the
statement-by-statement documentation.

* `Work.Landing.Core`, `Angles`, `Rays`, `Land` : definitions (family, angles, rays, landing
  inputs, lifted L-wake arcs `wakeArc`).
* `Work.Landing.Land.Main` : `rayAccum_image` (the ray transfer, from `IsDynBottcher` alone).
* `Work.Landing.Land.Landing` : `landsAt_image`, `landsAt_periodic`, `landsAt_unique`,
  `landsAt_pair_exchange`, `landsAt_repelling_or_parabolic` (Milnor 18.10, classification),
  `rootRays_period`, `landsAt_paramAngle_not_parabolic`, `landsAt_paramAngle_repelling`.
* `Work.Landing.Caratheodory.landsAt_of_extension`, `Work.Landing.Land.Caratheodory`
  (`PeriodicRaysLand_of_extension`, `exists_landsAt_repelling_or_parabolic`) : the existence half
  of the landing theorem, from the Carathéodory extension input.
* the remaining modules are the individual (mostly combinatorial) leaves.
-/
