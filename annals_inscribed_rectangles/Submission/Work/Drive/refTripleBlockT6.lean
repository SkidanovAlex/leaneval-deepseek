import Mathlib
import Submission.Work.Drive.refTripleRows
import Submission.Work.Drive.blockT6Wrapper_of_T6GenAtD
import Submission.Work.Drive.cutTransport
import Submission.Work.Drive.meet3Hyp_perm

/-!
# The transport `T6` at the two configuration blocks of the reference triple

This module supplies the two **`Odd (topBdryMeet ·) ↔ …`** conjuncts of
`Work.Drive.refTripleAt_blockT6At` (the clause-`6` chapter of `Work.Drive.hn2_refTripleAt_producer`)
in the form the **corrected** per-block transport wrapper consumes.

The clone `Drive/refTripleTransport.lean.txt` contained the block-`0` instance for the *stale* wrapper
`Work.Drive.odd_topBdryMeet_zero_iff_of_T6GenAtDBox_meet3Hyp`, which is one level band short
(`WALL_NODES_H3_STATUS.md` §5, `ENCODED_FAMILY_STATUS.md` §7.4): the avoidance `ftY2 x ≠ 0` needs
`c₁ < levelOf (Q z)` on the disk, not the `≠ c₂` form.  The corrected wrapper is
`Work.Drive.blockT6Wrapper_of_T6GenAtD`, and the strict bands `hlev₁`/`hlev₂` at the reference triple
are supplied by `Work.Drive.levelOf_chartPert_rotCapping_gt_core` (`Drive/refTripleLevelBand.lean`).

(The file could not be built before the `Work.Drive.mk3` duplicate was resolved — the reference-triple
vocabulary reaches `intersection_bordism3` and the transport `encodedTransverse`; see
`ASSEMBLY_CLASH_STATUS.md`.  With the duplicate names split apart the combination builds.)

The hypotheses split into three groups:

* the **geometric disjointness/level data** of the reference triple, all proved on disk
  (`refTripleRows.lean` §7–§9: `transport_disins_reference_block`, `transport_disins_reference_block'`,
  `chartPert_rotCapping_ne_refBlock_of_small`, `disjoint_range_refBlock_config_refPlane`);
* the **sweeps' `Meet3Hyp`** — the hypothesis `hM`, available from
  `Work.Drive.exists_sweepGenericity_opens` (`hn2_refTripleAt_producer.lean`);
* the **box bundle** `T6GenAtDBox` at the block — the hypothesis `hgen`, the open-dense genericity the
  enhanced Step A of the producer supplies.

Everything here is assembly: one application of the wrapper at the block, plus the relabelling
`Work.Drive.ncard_topBdryMeet_eq_perm` for block `1`.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 2000000

/-- **The T6 parity equivalence at block `0` of the reference triple.** -/
theorem refTriple_topBdryMeet_zero_iff {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam) (u v : UnitAddCircle)
    (cblk : Fin 3 → ℝ) (hcblk1 : 0 < cblk 1) (hcblk2 : 0 < cblk 2)
    (t : EuclideanSpace ℝ (Fin 12))
    (hM : Meet3Hyp CappingSpace
      (sweepChartFam (refTriple Q (refPlanePres φ lam hlam) u v)
        (fun s p => chartPert s p) cblk t))
    (hgen : T6GenAtDBox (fun z : ℂ => chartPert (blk 0 t) (rotCapping u (Q z)))
      (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 1)
      (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2)
      (cblk 1) (cblk 2))
    (hdisj₁ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 →
      chartPert (blk 0 t) (rotCapping u (Q z))
        ≠ refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 1 y)
    (hdisj₂ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 →
      chartPert (blk 0 t) (rotCapping u (Q z))
        ≠ refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2 y)
    (hdisj₁₂ : ∀ y y' : EuclideanSpace ℝ (Fin 2),
      refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 1 y
        ≠ refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2 y')
    (hlev₁ : ∀ z : ℂ, ‖z‖ ≤ 1 →
      cblk 1 < levelOf (chartPert (blk 0 t) (rotCapping u (Q z))))
    (hlev₂ : ∀ z : ℂ, ‖z‖ ≤ 1 →
      cblk 2 < levelOf (chartPert (blk 0 t) (rotCapping u (Q z)))) :
    (Odd (topBdryMeet CappingSpace
        (sweepChartFam (refTriple Q (refPlanePres φ lam hlam) u v)
          (fun s p => chartPert s p) cblk t) 0).ncard ↔
      Odd (coreSideCount (fun z : ℂ => chartPert (blk 0 t) (rotCapping u (Q z))) (cblk 1)
          (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 1)) ∧
        Odd (coreSideCount (fun z : ℂ => chartPert (blk 0 t) (rotCapping u (Q z))) (cblk 2)
          (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2))) := by
  have hQsm : IsSmoothChart Q := IsSmoothChart_of_isPlaneChart hQ
  have hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z := hQ.2.2.1
  have hRseam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y →
      refPlanePres φ lam hlam (seamInv2 y) = refPlanePres φ lam hlam y :=
    fun y hy => (refPlanePres_seam φ lam hlam y hy).symm
  -- the family of the wrapper is the `sweepChartFam` of the reference triple
  have hfam : (fun k : Fin 3 => clampedSweep
        (![cblk 0, cblk 1, cblk 2] k) (fun r => 1 - r)
        (![diskPlane (fun z : ℂ => chartPert (blk 0 t) (rotCapping u (Q z))),
            refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 1,
            refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2] k))
      = sweepChartFam (refTriple Q (refPlanePres φ lam hlam) u v)
          (fun s p => chartPert s p) cblk t := by
    funext k
    fin_cases k <;> rfl
  have hM' : Meet3Hyp CappingSpace
      (fun k => clampedSweep (![cblk 0, cblk 1, cblk 2] k) (fun r => 1 - r)
        (![diskPlane (fun z : ℂ => chartPert (blk 0 t) (rotCapping u (Q z))),
            refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 1,
            refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2] k)) := by
    rw [hfam]
    exact hM
  have hmain := blockT6Wrapper_of_T6GenAtD
    (fun z : ℂ => chartPert (blk 0 t) (rotCapping u (Q z)))
    (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 1)
    (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2)
    (cblk 0) (cblk 1) (cblk 2) hcblk1 hcblk2
    (contMDiff_chartPert_rotCapping hQsm u 0 t)
    (chartPert_rotCapping_seam hQseam u 0 t)
    (contMDiff_refBlock hQsm u v φ lam hlam t 1)
    (contMDiff_refBlock hQsm u v φ lam hlam t 2)
    (fun y hy => ((refBlock_seam Q (refPlanePres φ lam hlam) hQseam hRseam u v t 1 y hy)).symm)
    (fun y hy => ((refBlock_seam Q (refPlanePres φ lam hlam) hQseam hRseam u v t 2 y hy)).symm)
    hdisj₁ hdisj₂ hdisj₁₂ hlev₁ hlev₂ hM' hgen
  rw [hfam] at hmain
  exact hmain

/-- **The T6 parity equivalence at block `1` of the reference triple.**  The core chart is the
`v`-chart `z ↦ chartPert (blk 1 t) (rotCapping v (Q z))` and the two factors are read at the pair
`(refBlock 0, refBlock 2)` — the *transposed* labelling (the cyclic order would couple block `2` into
the block-`0` data, cf. `Drive/hdenseRelabel.lean`).  The relabelling of the top count is
`Work.Drive.ncard_topBdryMeet_eq_perm` at the transposition `(0 1)`, and the `Meet3Hyp` of the
transposed sweep family is `Work.Drive.meet3Hyp_perm`. -/
theorem refTriple_topBdryMeet_zero_iff_block1 {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam) (u v : UnitAddCircle)
    (cblk : Fin 3 → ℝ) (hcblk0 : 0 < cblk 0) (hcblk2 : 0 < cblk 2)
    (t : EuclideanSpace ℝ (Fin 12))
    (hM : Meet3Hyp CappingSpace
      (sweepChartFam (refTriple Q (refPlanePres φ lam hlam) u v)
        (fun s p => chartPert s p) cblk t))
    (hgen1 : T6GenAtDBox (fun z : ℂ => chartPert (blk 1 t) (rotCapping v (Q z)))
      (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0)
      (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2)
      (cblk 0) (cblk 2))
    (hdisj₁ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 →
      chartPert (blk 1 t) (rotCapping v (Q z))
        ≠ refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0 y)
    (hdisj₂ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 →
      chartPert (blk 1 t) (rotCapping v (Q z))
        ≠ refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2 y)
    (hdisj₁₂ : ∀ y y' : EuclideanSpace ℝ (Fin 2),
      refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0 y
        ≠ refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2 y')
    (hlev₁ : ∀ z : ℂ, ‖z‖ ≤ 1 →
      cblk 0 < levelOf (chartPert (blk 1 t) (rotCapping v (Q z))))
    (hlev₂ : ∀ z : ℂ, ‖z‖ ≤ 1 →
      cblk 2 < levelOf (chartPert (blk 1 t) (rotCapping v (Q z)))) :
    (Odd (topBdryMeet CappingSpace
        (sweepChartFam (refTriple Q (refPlanePres φ lam hlam) u v)
          (fun s p => chartPert s p) cblk t) 1).ncard ↔
      Odd (coreSideCount (fun z : ℂ => chartPert (blk 1 t) (rotCapping v (Q z))) (cblk 0)
          (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0)) ∧
        Odd (coreSideCount (fun z : ℂ => chartPert (blk 1 t) (rotCapping v (Q z))) (cblk 2)
          (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2))) := by
  have hQsm : IsSmoothChart Q := IsSmoothChart_of_isPlaneChart hQ
  have hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z := hQ.2.2.1
  have hRseam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y →
      refPlanePres φ lam hlam (seamInv2 y) = refPlanePres φ lam hlam y :=
    fun y hy => (refPlanePres_seam φ lam hlam y hy).symm
  -- the transposed family
  have hfam : (fun k : Fin 3 => clampedSweep
        (![cblk 1, cblk 0, cblk 2] k) (fun r => 1 - r)
        (![diskPlane (fun z : ℂ => chartPert (blk 1 t) (rotCapping v (Q z))),
            refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0,
            refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2] k))
      = fun i : Fin 3 => sweepChartFam (refTriple Q (refPlanePres φ lam hlam) u v)
          (fun s p => chartPert s p) cblk t (Equiv.swap 0 1 i) := by
    funext k
    fin_cases k <;> rfl
  -- the `Meet3Hyp` of the transposed family, from the reference one by the transposition
  have hEE : (fun k : Fin 3 => clampedSweep
        (![cblk 1, cblk 0, cblk 2] ((Equiv.swap 0 1) k)) (fun r => 1 - r)
        (![diskPlane (fun z : ℂ => chartPert (blk 1 t) (rotCapping v (Q z))),
            refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0,
            refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2]
          ((Equiv.swap 0 1) k)))
      = sweepChartFam (refTriple Q (refPlanePres φ lam hlam) u v)
          (fun s p => chartPert s p) cblk t := by
    funext k
    fin_cases k <;> rfl
  have hM' : Meet3Hyp CappingSpace
      (fun k => clampedSweep (![cblk 1, cblk 0, cblk 2] k) (fun r => 1 - r)
        (![diskPlane (fun z : ℂ => chartPert (blk 1 t) (rotCapping v (Q z))),
            refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0,
            refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2] k)) :=
    meet3Hyp_perm _ (Equiv.swap 0 1) (by rw [hEE]; exact hM)
  have hmain := blockT6Wrapper_of_T6GenAtD
    (fun z : ℂ => chartPert (blk 1 t) (rotCapping v (Q z)))
    (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0)
    (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2)
    (cblk 1) (cblk 0) (cblk 2) hcblk0 hcblk2
    (contMDiff_chartPert_rotCapping hQsm v 1 t)
    (chartPert_rotCapping_seam hQseam v 1 t)
    (contMDiff_refBlock hQsm u v φ lam hlam t 0)
    (contMDiff_refBlock hQsm u v φ lam hlam t 2)
    (fun y hy => ((refBlock_seam Q (refPlanePres φ lam hlam) hQseam hRseam u v t 0 y hy)).symm)
    (fun y hy => ((refBlock_seam Q (refPlanePres φ lam hlam) hQseam hRseam u v t 2 y hy)).symm)
    hdisj₁ hdisj₂ hdisj₁₂ hlev₁ hlev₂ hM' hgen1
  -- transport the top count across the transposition `(0 1)`
  have hperm := ncard_topBdryMeet_eq_perm
    (sweepChartFam (refTriple Q (refPlanePres φ lam hlam) u v)
      (fun s p => chartPert s p) cblk t) (Equiv.swap 0 1)
  rw [show (Equiv.swap 0 1) 0 = (1 : Fin 3) from by decide] at hperm
  rw [hfam] at hmain
  rw [hperm] at hmain
  exact hmain

end

end Work.Drive
