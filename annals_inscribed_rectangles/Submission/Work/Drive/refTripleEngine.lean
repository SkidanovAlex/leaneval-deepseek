import Mathlib
import Submission.Work.Drive.endsNoRegular
import Submission.Work.Drive.sweepTripleGeneric
import Submission.Work.Drive.chartShiftEngineInput
import Submission.Work.Drive.orderTripleParity

/-!
# The engine's output `Odd (Σ top)` for the design's *perturbed* family, from `Meet3Hyp` and the
# class-triple parity alone

This file packages the first of the two heavy inputs of the `hn2`/`hdense` assembly
(`Work.Drive.cntAt_pair_eq_one_of_threeBlockT6`, `hn2Reference.lean`) — the oddness of the total *top*
boundary count of the perturbed triple — in the weakest form:

> **`Work.Drive.odd_sum_topBdryMeet_sweepChartFam`**:
> `Meet3Hyp CappingSpace (sweepChartFam P Ξ c t)` and `Odd (classTripleSet P')`, where `P'` is the
> perturbed plane presentation `fun k z => Ξ (t k) (P k z)`, give
> `Odd (Σ_k #(topBdryMeet_k))`.

The two inputs are exactly what the design's other lanes deliver:

* `Meet3Hyp` — the Sard route (`Work.Drive.exists_meet3Hyp_sweepChartFam_of_locus`, whose remaining
  hypothesis is the chart containment `hloc`, cf. `Drive/refTripleHloc.lean`);
* `Odd (classTripleSet P')` — the linearization lane (`Work.Drive.odd_ncard_classTripleSet_of_hasClassLinearization`).

**The `hdisj` (seam/slice separation) and `hbot` (ends clause) inputs are discharged here and need no
hypothesis**: the first is free from `Meet3Hyp` (`Work.Drive.hdisj_of_meet3Hyp`), and the second is
`Work.Drive.odd_sum_bottomBdryMeet_of_classTripleSet` (`Drive/endsNoRegular.lean`), which does **not**
need `ClassTripleRegular` — this is what removes the `hci` obstruction of
`HC_VS_PLANE_IMMERSION.md` §2 from the ends lane.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The engine plus the ends clause, for the design's perturbed family.** -/
theorem odd_sum_topBdryMeet_sweepChartFam
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (c : Fin 3 → ℝ) (t : EuclideanSpace ℝ (Fin 12))
    (hcpos : ∀ k : Fin 3, 0 < c k)
    (hc1 : c 1 < c 0) (hc2 : c 2 < c 0)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      c 0 < levelOf ((fun z => Ξ (blk k t) (P k z)) y))
    (hmeet : Meet3Hyp CappingSpace (sweepChartFam P Ξ c t))
    (hodd : Odd (classTripleSet (fun k => fun z => Ξ (blk k t) (P k z))).ncard) :
    Odd ((topBdryMeet CappingSpace (sweepChartFam P Ξ c t) 0).ncard
      + (topBdryMeet CappingSpace (sweepChartFam P Ξ c t) 1).ncard
      + (topBdryMeet CappingSpace (sweepChartFam P Ξ c t) 2).ncard) := by
  have hD : sweepChartFam P Ξ c t
      = fun k => clampedSweep (c k) (fun r => 1 - r) (fun z => Ξ (blk k t) (P k z)) := rfl
  have hbot := odd_sum_bottomBdryMeet_perturbedPlanes P Ξ (fun k => blk k t) c
    hcpos hc1 hc2 hlev hodd
  rw [hD] at hmeet ⊢
  exact odd_sum_topBdryMeet_of_ends _ hmeet
    (fun k x hx => hdisj_of_meet3Hyp _ hmeet k x hx) hbot

/-- **The engine plus the ends clause, for the design's *honest* chains** — the `htop` input of the
honest route (`hdense`'s `Work.Drive.hdense_identity_of_design_data`), with the same hypotheses as the
perturbed form but on the unperturbed chains.

Its point is that **no `ClassTripleRegular` datum appears**: the engine's `Meet3Hyp` is supplied by the
angle-genericity (the transport's `(G2)`), the seam/slice separation is free from it, and the ends
clause is the sharpened `Work.Drive.odd_sum_bottomBdryMeet_of_classTripleSet`.  Hence this lemma is
available for the honest chart of *every* smooth Jordan curve, including those whose class map fails
the immersion `hci` of `ClassTripleRegular` (`HC_VS_PLANE_IMMERSION.md` §2). -/
theorem odd_sum_topBdryMeet_clampedSweep
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (c : Fin 3 → ℝ)
    (hcpos : ∀ k : Fin 3, 0 < c k)
    (hc1 : c 1 < c 0) (hc2 : c 2 < c 0)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < levelOf (P k y))
    (hmeet : Meet3Hyp CappingSpace
      (fun k => clampedSweep (c k) (fun r => 1 - r) (P k)))
    (hodd : Odd (classTripleSet P).ncard) :
    Odd ((topBdryMeet CappingSpace
            (fun k => clampedSweep (c k) (fun r => 1 - r) (P k)) 0).ncard
      + (topBdryMeet CappingSpace
            (fun k => clampedSweep (c k) (fun r => 1 - r) (P k)) 1).ncard
      + (topBdryMeet CappingSpace
            (fun k => clampedSweep (c k) (fun r => 1 - r) (P k)) 2).ncard) := by
  have hbot := odd_sum_bottomBdryMeet_of_classTripleSet P c (fun r => 1 - r)
    (by norm_num) (by norm_num)
    (fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩)
    (continuous_const.sub continuous_id).continuousOn
    (fun a ha b hb hab => by dsimp only; linarith)
    hcpos hc1 hc2 hlev hodd
  exact odd_sum_topBdryMeet_of_ends _ hmeet
    (fun k x hx => hdisj_of_meet3Hyp _ hmeet k x hx) hbot

end

end Work.Drive
