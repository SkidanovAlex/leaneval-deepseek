import Mathlib
import Submission.Work.Drive.sweepBlurFacts
import Submission.Work.Drive.sweepLoopChamfer_ftc_top

/-!
# The loop helpers of the chamfered sweep (minimal restoration of a pruned module)

The module `Submission.Work.Drive.sweepFam_slices_knots` was deleted from the tree by the pruning of
2026-09-25.  That module contained, besides elementary loop helpers, the *unconditional* slices
clause `Work.Drive.sweepFam_slices_knots` (injectivity of every slice on one period from `havoid`
alone).  That clause is one of the open pins of the sweep route — it is *not* reproved here and
nothing below claims it.

Several modules that belong to the import closure of the **top end** of the chord sweep
(`sweepLoopChamfer_ftc`, `chamferVel_hasDerivAt`, `widePhaseForm`, `sweepFam_double_blur_deriv`,
`sweepWideEndCore`, …) need only the elementary helpers that used to live in the deleted module:

* `Work.Drive.sweepUnwrap` — the unwrapped chamfered loop (with the four `sweepArc'`/`sweepChord'`
  branches);
* `Work.Drive.sweepUnwrap_continuous`;
* `Work.Drive.sweepLoopChamfer_eq_unwrap`;
* `Work.Drive.sweepLoopChamfer_continuous_t`;
* and (transitively, via `sweepBlurFacts`) `Work.Drive.sweepBump_nonneg`.

All of them are *already proved* in `Submission/Work/Drive/sweepLoopChamfer_ftc_top.lean`, the
self-contained copy written precisely to avoid the import of the deleted module (there the same four
items appear under the `…Top` names).  They are re-established here under their original names, with
the definition of `sweepUnwrap` copied verbatim so that `rw [sweepUnwrap]`-style unfolding in the
consumers keeps working, exactly as it did before the pruning.

This file exists only so that the modules of the closure compile again; it is a restoration, not new
mathematics.
-/

noncomputable section
namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

/-- The unwrapped chamfered sweep loop: the four branches of `sweepLoopChamfer` as a function of the
profile parameter `u`.  Verbatim copy of the definition that used to live in this module (the
`…Top` twin `sweepUnwrapTop` in `sweepLoopChamfer_ftc_top.lean` has the same body). -/
noncomputable def sweepUnwrap (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s u : ℝ) : Space :=
  if u ≤ 1 / 2 then sweepArc' r D s (lam + (1 - 2 * lam) * (2 * u))
  else if u ≤ 1 / 2 + lam / 2 then
    (1 - (2 * u - 1) / lam) • sweepArc' r D s (1 - lam)
      + ((2 * u - 1) / lam) • sweepChord' r D s (1 - lam)
  else if u ≤ 1 - lam / 2 then
    sweepChord' r D s (1 - lam - (u - (1 / 2 + lam / 2)) / (1 / 2 - lam) * (1 - 2 * lam))
  else
    (1 - (u - (1 - lam / 2)) / (lam / 2)) • sweepChord' r D s lam
      + ((u - (1 - lam / 2)) / (lam / 2)) • sweepArc' r D s lam

/-- `sweepLoopChamfer` is the unwrapped loop composed with the profile parameter.  (Same statement
and same `rfl` proof as the original.) -/
lemma sweepLoopChamfer_eq_unwrap (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s t : ℝ) :
    sweepLoopChamfer r D lam s t = sweepUnwrap r D lam s (sweepParam t) := rfl

/-- Continuity of the unwrapped loop in the profile parameter. -/
theorem sweepUnwrap_continuous (r : ℝ → Space)
    (hr : Continuous r) {d : BandArcData} (D : SweepData d) {lam s : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) :
    Continuous (fun u : ℝ => sweepUnwrap r D lam s u) :=
  sweepUnwrap_continuousTop r hr D hlam0 hlam1

/-- Continuity of the chamfered loop in the loop parameter. -/
theorem sweepLoopChamfer_continuous_t {r : ℝ → Space}
    (hr : Continuous r) {d : BandArcData} (D : SweepData d) {lam s : ℝ}
    (hlam0 : 0 < lam) (hlam1 : lam < 1 / 2) :
    Continuous (fun t : ℝ => sweepLoopChamfer r D lam s t) :=
  sweepLoopChamfer_continuous_tTop hr D hlam0 hlam1

end Work.Drive
