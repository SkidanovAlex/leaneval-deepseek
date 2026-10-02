/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Submission/Work/PARIMPL2/` — the area, in one import

```lean
import Submission.Work.PARIMPL2.All
```

## What the area is

`Submission/Work/PARIMPL2/` constructs the **three data bundles** of the delivered area
`Submission/Work/PARIMPL/` — `MatchData`, `TransitData`, `LeakData` — and the assembled
`ParImplInputs`, from the **sibling exports** of the other areas (FlowerGlue, ELAssembly, root/seed,
NAKANE, GATE2), so that `Work.PARIMPL.noPath` and `Work.PARIMPL.ParImplInputs.impl` become
unconditional modulo those exports.  The hypothesis list is in `NOTES.md` §2.

## Chain A (the deliverable) and chain B (insurance)

* **Chain A** — `Work.PARIMPL2.Data` + `Work.PARIMPL2.Main`: the *delivered* structures
  `Work.PARIMPL.{MatchData, TransitData, LeakData, ParImplInputs}`, built from the sibling
  hypothesis list `Work.PARIMPL2.SiblingInputs`.  `Work.PARIMPL2.parImplInputs d P fl h` is the
  holder structure; `Work.PARIMPL.ParImplInputs.noPath` and `.impl` then give the endgame
  (`Work.PARIMPL2.noPathPARIMPL`, `Work.PARIMPL2.implPARIMPL` are the same statements spelled
  out).  This chain *is* the deliverable: after the repairs recorded in
  `Submission/Work/PARIMPL/NOTES.md` §0.0, the delivered structures are the corrected ones.
* **Chain B** — `Work.PARIMPL2.DefsFix` + `Work.PARIMPL2.PathFix` + `Work.PARIMPL2.FixMain`: the
  same three bundles and holder structure as *private copies* of this area (with the corrected
  comparisons), together with self-contained re-proofs of `blowup`, `height`, `escape_one`,
  `transit_crossing`, `noPath` and `impl`.  It is kept as **insurance**: it does not depend on the
  `Submission/Work/PARIMPL/Match.lean` edit having landed, so
  `Work.PARIMPL2.noPath` / `Work.PARIMPL2.implFix` remain available even if that edit is reverted.
  A caller who has the repaired PARIMPL should use chain A.

## The findings (see the `NOTES_FALSE_*.md` files)

* `NOTES_FALSE_match_in.md` — `Work.PARIMPL.MatchData.match_in` compares the Écalle heights with
  the wrong sign (the model's `approxEcal` is a *decreasing* Abel coordinate,
  `Work.PARIMPL.approxEcal_step_rot`, while the flower's `φa`/`Ψ` are increasing; the (T-e) field's
  `Re β = -1/2` is the reflection constant of the flower's `+1/2`);
* `NOTES_FALSE_match_out.md` — the same for `match_out`;
* `NOTES_FALSE_te.md` — the (T-e) item required a *constant* `β` on the whole transit strip,
  which is not satisfiable (the reflection discrepancy vanishes at the strip's midpoint and is
  `≈ −1/2` at its ends); repaired to the two windows;
* `NOTES_FALSE_ExitTrackedLoc.md` — `Work.PARIMPL.ExitTrackedLoc` **was vacuous** (machine-checked:
  `Xo` existential, window empty; repaired on 2026-09-28), and `Work.PARIMPL.TransitLockstep`
  quantifies its box origin existentially; `Work.PARIMPL2.ExitTrackedWindow` /
  `Work.PARIMPL2.LockstepAll` are the repaired forms.

## Modules

| module | content |
|---|---|
| `Work.PARIMPL2.ExitTracking` | `LockstepAll` (the design's uniform lock-step transit), `ExitTrackedWindow` (the repaired bounded-window exit), `transitLockstep_of_lockstepAll` |
| `Work.PARIMPL2.Inputs` | the sibling hypothesis list: `MatchExport` (= `MatchCore`), `TransitExport`, `LeakExport`, `SiblingInputs` |
| `Work.PARIMPL2.Data` | chain A: `matchData`, `transitData`, `leakData`, `exists_deepDisc` |
| `Work.PARIMPL2.Main` | chain A: `parImplInputs`, `implPARIMPL`, `noPathPARIMPL` |
| `Work.PARIMPL2.MatchCore` | the MATCH comparison as a **coordinate identity**: `match_in_of_coord`, `match_out_of_coord` (the two height comparisons *derived*), `matchData_of_core` |
| `Work.PARIMPL2.SignObstruction` | the formal core of the sign finding: `coeff_eq_neg_one_of_abel`, `im_const_of_im_eq_of_coeff`, `false_of_stated_orientation` |
| `Work.PARIMPL2.DefsFix` | chain B: the corrected `MatchData`, `TransitData`, `LeakData`, `ParImplInputs`, with `blowup`, `height`, `escape_one` |
| `Work.PARIMPL2.PathFix` | chain B: `transit_crossing`, `noPath` |
| `Work.PARIMPL2.FixMain` | chain B: `matchDataFix`, `transitDataFix`, `leakDataFix`, `parImplInputsFix`, `implFix`, `noPathFix` |
| `Work.PARIMPL2.exitTrackedWindow_of_lockstep` | (delegated) `LockstepAll ⟹ ExitTrackedWindow` |
| `Work.PARIMPL2.escape_of_exitTrackedWindow` | (delegated) `ExitTrackedWindow` + the depth give the escape |
| `Work.PARIMPL2.approxEcal_end_in_small`, `…_out_small` | (delegated) the small-`ζ` model asymptotics on the two windows (`O(λ²/‖ζ‖³)`) |
| **`Work.PARIMPL2.coord_in_of_estimates`** | (delegated) FlowerGlue's estimate + the model asymptotic + the chart consistency ⟹ the incoming coordinate identity |
-/
import Submission.Work.PARIMPL2.ExitTracking
import Submission.Work.PARIMPL2.Inputs
import Submission.Work.PARIMPL2.Data
import Submission.Work.PARIMPL2.Main
import Submission.Work.PARIMPL2.SignObstruction
import Submission.Work.PARIMPL2.DefsFix
import Submission.Work.PARIMPL2.PathFix
import Submission.Work.PARIMPL2.FixMain
import Submission.Work.PARIMPL2.exitTrackedWindow_of_lockstep
import Submission.Work.PARIMPL2.escape_of_exitTrackedWindow
import Submission.Work.PARIMPL2.approxEcal_end_in_small
import Submission.Work.PARIMPL2.approxEcal_end_out_small
import Submission.Work.PARIMPL2.coord_in_of_estimates

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

