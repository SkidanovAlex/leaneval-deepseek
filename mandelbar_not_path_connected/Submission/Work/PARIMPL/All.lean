/-
Copyright: subproject `Submission/Work/PARIMPL/` of `mandelbar_not_path_connected`.

# `Submission.Work.PARIMPL` — aggregator

Import this module to get the whole chapter `Submission/Work/PARIMPL/`:

* `Work.PARIMPL.ParNormal` — the **parameter normal form** (HS Prop. 4.1, uniform in `c`) and
  the three sides `Nm` (`a₂ < 0`), `Par` (`a₂ = 0`), `Np` (`a₂ > 0`);
* `Work.PARIMPL.MatchData` — **MATCH**: the local model vs. the Leau–Fatou flower at `c₀`
  ((M-in), (M-out), (T-e)), with the `FatouCoord` fix (`FlowerFix`: `φa_shift`, `Pg`) and the
  `Z`-decay (`ZDecay`) as named hypotheses;
* `Work.PARIMPL.TransitData` — **TRANS**: the transit coordinate `transU`, its continuity, its
  **phase blow-up** (`TransitData.blowup`, derived) and its **height** (`TransitData.height`,
  derived), plus the exit matching;
* `Work.PARIMPL.LeakData` — **LEAK**: the robust leak disc, the (I2) robustness and
  `trans_escape`, with the NAKANE input `GreenEscapeOpen` (joint continuity of the Green
  function);
* `Work.PARIMPL.noPath` — **PATH**: the path form of `hLB`;
* `Work.PARIMPL.ParImplInputs` — the holder structure with `Nm`, `impl` and `noPath`;
* the rotated step estimates `Work.PARIMPL.approxEcal_step_rot` and
  `Work.PARIMPL.approxEcal_transit_rot` (the `h(0) = e^{iθ}` versions of the `Implosion` estimates)
  and the algebraic core `Work.PARIMPL.norm_S_le_rot`;
* `Work.PARIMPL.periodFiveGone` — the disappearance of the period-`5` point on `Nm`;
* `Work.PARIMPL.robust_of_greenOpen` — (I2), the robustness of the leak disc, *derived* from the
  NAKANE input `GreenEscapeOpen` and the depth of the leak disc (`LeakData.deep`);
* `Work.PARIMPL.continuousOn_transU` — the continuity of the transit coordinate (§1.3), *derived*
  from the continuity of the orbit and the two slit-plane conditions on the Écalle logarithms (so
  that the `cont` field of `TransitData` can be discharged from `MatchData.entering`);
* `Work.PARIMPL.flowerFix_of_fatouCoordFix`, `Work.PARIMPL.exists_flowerFix` — the `FatouCoordFix`
  input `FlowerFix` of §1.2 (`φa_shift`, the `g`-invariant half-petal `Pg`) is *derived* from the
  delivered `Work.FatouCoordFix.ParabolicFlowerFix`; `exists_flowerFix` also produces the flower
  itself, so `FlowerFix` is no longer an assumption;
* `Work.PARIMPL.Nm_mem_closure` — `c₀ ∈ closure P.Nm`: the implosion side accumulates at the
  root parameter (from the FBif bifurcation side `Work.FBif.bifSide`), i.e. the non-vacuity of
  `Nm` (this is the `c_mem_closure` field of `ImplSide`);
* **`Work.PARIMPL.exists_parNormal`** — the existence of the parameter normal form, i.e. HS
  Prop. 4.1 uniform in `c`, hence *non-vacuity* of the whole chapter: for every root-parabolic
  parameter `d` there is a `P : ParNormal d`.  Proved in the sub-chapter
  `Submission/Work/PARIMPL/ParSplit/` (imported here): `ParSplit.splitPair_exists` (the splitting
  of the parabolic fixed point, contour integrals + the argument principle),
  `ParSplit.wall_factorization` (the real wall function `G = A·h`), `ParSplit.PackSplit` (the
  `SplitData`), and the assembly `ParSplit.parNormal_of_splitData` (the chart `m + s·ζ`, the germ
  `parHgerm`, its continuity `ParSplit.parChart_continuity` and its uniform bounds
  `ParSplit.parHgerm_bounds`), with the numerical/phase analysis of the collision locus
  (`ParSplit.parU0_phase`, `ParSplit.parU0_eq_one_of_wall`: `parHgerm c 0 → 1` at the wall).

For the `Work.Final` vocabulary (`ImplosionSide`, the `FinalInputs` field shape) use
`Submission.Work.PARIMPL.Bridge` — a *separate* module, because it imports
`Submission.Work.Final.Defs`; do not import it from a file that `Final.Defs` (transitively)
imports.  For the same reason `Work.PARIMPL.leak_shift_int` (the shift-invariance of the equator
leak, which imports `Work.Final.equatorLeak_shift`) is *not* imported here.

Axiom-cleanliness of everything listed here (plus of `Bridge`, `leak_shift_int` and the whole
`ParSplit/` sub-chapter) is recorded by the three check modules `_axcheck.lean`,
`_axcheck_final.lean` and `ParSplit/_axcheck.lean` (36 `#print axioms`, all
`[propext, Classical.choice, Quot.sound]`).
-/
import Submission.Work.PARIMPL.Basic
import Submission.Work.PARIMPL.Match
import Submission.Work.PARIMPL.Transit
import Submission.Work.PARIMPL.Leak
import Submission.Work.PARIMPL.Path
import Submission.Work.PARIMPL.Main
import Submission.Work.PARIMPL.periodFiveGone
import Submission.Work.PARIMPL.norm_S_le_rot
import Submission.Work.PARIMPL.approxEcal_step_rot
import Submission.Work.PARIMPL.approxEcal_transit_rot
import Submission.Work.PARIMPL.robust_of_greenOpen
import Submission.Work.PARIMPL.continuousOn_transU
import Submission.Work.PARIMPL.flowerFix_of_fatouCoordFix
import Submission.Work.PARIMPL.exists_flowerFix
import Submission.Work.PARIMPL.exists_parNormal
import Submission.Work.PARIMPL.Nm_mem_closure

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL

end Work.PARIMPL
