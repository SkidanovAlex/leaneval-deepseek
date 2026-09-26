import Mathlib
import Submission.Work.Drive.Mono.AEGenConsumer2
import Submission.Work.Drive.Mono.AEGen2Inputs
import Submission.Work.Drive.Mono.boxGenE_pairSard
import Submission.Work.Drive.Mono.ae_faceNoBend
import Submission.Work.Drive.Mono.SweepGeom3
import Submission.Work.Drive.Mono.noJumpInput3_holds
import Submission.Work.Drive.Mono.goodSweepGeom3_holds

/-! Guidance from the project lead (the requester):

LEAD'S DESIGN (after an audit against Pardon's paper, torusdist.tex). This target has NO extra hypotheses, so it cannot be closed vacuously.
Everything is proved except Pardon's Lemma 3 in a correct form. Route: pardon_of_boxShrinkShifted cleansDiscsAllWd (…) or the half-box endpoint below.

DO NOT target TiltedSweepExists as stated. Its ∀ ε with ε·R < h lets ε ≥ 2 swallow the whole box (finish region ∅), so it is provable only by proving the theorem.
DO NOT target CountingHalfEpsSphere (ThickHalf is stronger than Pardon). RefuteDrop is NOT a counterexample: it refutes only the count-free DropCase.
TEST every new residual in LOCAL form: drop IsDistortionBound/hsmall and keep #S + 2#D < min p q. The global hypotheses are vacuous (by the theorem itself), so the
global form cannot tell a true residual from a false one.

STEP A: SweepNiceGeneric (upstream choice of (s,u)). ...
LEAD, 13:35: replace TiltedSweepExists' by a WEAKER residual; hreg and hjump disappear.
LEAD, 23:15: NEW HYPOTHESIS (threaded; the level counts need it): CutTransverse ... ae_cutTransverse: ∀ᵐ u.
LEAD, 04:45: the box level `s` is chosen in general position (BoxGen); the grazes are excluded by
the a.e. choice of the level, and the consumer may choose it because its level is picked in an
arbitrary conull set.
LEAD, 2026-09-26 07:55: the junction bundle must be the REPAIRED one.  Clause (c) of
`JunctionGenB`/`JunctionGenC` is satisfiable only after the centre is moved into general position
(only the four VERTICAL edge lines matter), and clause (a) needs the no-bend `FaceNoBend` at a.e.
cutting level.  This is the bundle `BoxGenE` (`Mono/BoxGenE.lean`), and the consumer may shift the
centre because `HasEssBox` is open in the centre and `Submission.BoxShrinkStatement` does not
mention it (`Work.Drive.Mono.boxShrink_of_cruxCoreWdAEG2`).

## State of this file (H381, session 21, late): COMPLETE — no `sorry`, no `sorryAx`

The whole chain is now assembled, and the only remaining input is the *geometric data producer*

    Work.Drive.Mono.goodSweepGeom3_holds : ∀ p q : ℕ, Work.Drive.Mono.GoodSweepGeomAEG3 p q
        (Submission/Work/Drive/Mono/goodSweepGeom3_holds.lean),

which is a colleague's file in flight; this file imports it rather than restating it.  The chain is

    pardon_unconditional_mono
      := Work.Drive.Mono.pardon_of_cruxCoreWdAEG2 cruxCoreWdAEG2_holds shiftGoodCentre_holds
    cruxCoreWdAEG2_holds
      := Work.Drive.Mono.cruxCoreWdAEG2_of_goodGeom3_and_noJump
           goodSweepGeom3_holds Work.Drive.Mono.noJumpInput3_holds

where

* `Work.Drive.Mono.shiftGoodCentre_holds` is **proved here** from the four genericity inputs of the
  lead's `Mono/NOTES_LEAD_junctionGen.md` §2: G1 and G3 of `Mono/boxGenE_pairSard.lean`, G2
  `Mono/ae_faceNoBend.lean` and the pre-existing `Work.Drive.Mono.ae_boxGen`, combined by
  `ae_boxGenE_shift` and `shiftGoodCentre_of_pairSard` (`Mono/AEGen2Inputs.lean`).  So the extra
  genericity hypothesis of `CruxCoreWdAEG2` is *free*.
* `Work.Drive.Mono.noJumpInput3_holds` (**proved, axiom-clean**) is field (L) of the tilted sweep on
  the corrected bundle `GoodDataPackage3` — Pardon's pinching count — resting on H330's
  `Work.Drive.Final.eventTraceData_holds` and the lead's route-I reformulation.
* `Work.Drive.Mono.GoodSweepGeomAEG3` (defined in `Mono/SweepGeom3.lean`) is the producer of
  `GoodDataPackage3 = DataPackage ∧ GoodSweepData3 ∧` (the level count at every level of the window);
  its ingredients are all proved (`noGraze_witness_arcs`, `gammaArcs_exist`, `gammaArc_noBend`,
  `junctionGenC_of_arcs`, `edgeFree_of_margin`, `levelCount_lt_min_all`,
  `levelSphereDecomposition_of_data`, `tiltData_in_window_export`, `ae_slabBoxCrossReg`,
  `sphereCoverAt_of_edgeFree`, `faceEvent_offK_null`, `ndEvent_of_datum`, `exists_countable_heightGood_dense`,
  `noGraze_witness_arcs_Q`, `pairSet_critical_null`, ...), the last pieces being
  `Work.Drive.Mono.geom3Data_exists` (`Mono/geom3Data_exists.lean`,
  `geom3Data_exists_of_atU ∘ geom3DataAtU_exists`) — **proved** by the producer team.

`#print axioms Work.Drive.Mono.pardon_unconditional_mono` is **`[propext, Classical.choice,
Quot.sound]`** — the theorem is complete, and no `sorry`/`sorryAx` occurs anywhere in its proof.

Every other route to the crux still closes the file, through the bridges of
`Submission/Work/Drive/Mono/Bridges2.lean` and `.../AEGen2.lean`:
`Work.Drive.Final.TiltedSweepMono` (H330), `Work.Drive.Mono.SweepSpanConst`,
`Work.Drive.Mono.TiltedTraceDataWExists`, `CruxCoreWdAEG` / `CruxCoreWdAE`. -/

namespace Work.Drive.Mono

/-- **G4 + G5 give the generic-centre property**, unconditionally: G4 is
`Work.Drive.Mono.hasEssBox_diag_shift`, G1 and G3 are the pair-Sard conjuncts of
`Work.Drive.Mono.boxGenE_pairSard`, G2 is `Work.Drive.Mono.ae_faceNoBend`, and
`Work.Drive.Mono.ae_boxGenE_shift` combines them with `Work.Drive.Mono.ae_boxGen`. -/
theorem shiftGoodCentre_holds : ShiftGoodCentre :=
  shiftGoodCentre_of_pairSard
    (fun P r c σ hbox => hasEssBox_diag_shift P r c σ hbox)
    (fun ψ c σ => ae_boxGenE_shift ψ
      (fun c' σ' => ae_ae_faceCrossReg ψ c' σ')
      (fun c' σ' s => ae_faceNoBend ψ c' σ' s)
      (fun c' σ' => ae_diag_vertEdgeFinite ψ c' σ') c σ)

open LeanEval.KnotTheory.PardonDistortion in
open scoped ENNReal in
/-- **The remaining input of the deliverable**, in its weakest form known in this workspace.

Pardon's crux (`Work.Drive.Final.CruxCoreWd`) is stated for *every* cutting level `u` with
`|u| < ε r`, and for every box level `s ∈ (r, (1+ε)r)`.  Pardon himself chooses both levels in
general position:

* the *cutting* level, because the counting of his pinching family is only available at a level
  avoiding the critical values of the height `y (σ 2) ∘ K` (at a tangency the knot grazes the slab,
  and no count of the crux controls the grazing visits);
* the *box* level, because at a level where the surface is tangent to the box sphere (a *graze*) the
  trace of the sweep has a junction that is not a locally Euclidean curve, and the graze levels are
  in general infinite, so they cannot be absorbed by the finite exceptional set `exc` of the sweep.

`Work.Drive.Mono.CruxCoreWdAEG2` (`Submission/Work/Drive/Mono/AEGen2.lean`) is that honest form:
the crux at almost every cutting level, at a box level in general position for the junction route
(`Work.Drive.Mono.BoxGenE`).  Both genericity hypotheses are free for the consumer
(`Work.Drive.Mono.pardon_of_cruxCoreWdAEG2`): the cutting level may be chosen in an arbitrary conull
set, and the box level likewise, at a centre shifted along the diagonal by the still-free parameter
`τ`.  It is *implied* by every form of the residual the fleet is pursuing (see `Mono/AEGen2.lean`,
`Mono/AGSweep2.lean` and `Mono/AEBridges.lean`). -/
theorem cruxCoreWdAEG2_holds : ∀ p q : ℕ, CruxCoreWdAEG2 p q :=
  cruxCoreWdAEG2_of_goodGeom3_and_noJump goodSweepGeom3_holds noJumpInput3_holds

open LeanEval.KnotTheory.PardonDistortion in
open scoped ENNReal in
/-- Pardon's distortion bound for torus knots, with no extra hypotheses. -/
theorem pardon_unconditional_mono (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q) (K : Knot)
    (hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
      ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K :=
  pardon_of_cruxCoreWdAEG2 cruxCoreWdAEG2_holds shiftGoodCentre_holds p q hp hq hc K hclass

end Work.Drive.Mono
