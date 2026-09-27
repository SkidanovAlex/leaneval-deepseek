import Mathlib
import Submission.Work.Drive.refTripleEngine
import Submission.Work.Drive.hn2Reference

/-!
# Endpoint: the antisymmetry of the germ side value at one angle, from the reference-triple data

This file is the **endpoint of the `hn2` lane**: it composes the three proved pieces

1. `Work.Drive.odd_sum_topBdryMeet_sweepChartFam` (`Drive/refTripleEngine`) — the engine plus the ends
   clause for the perturbed reference triple, from `Meet3Hyp` and `Odd (classTripleSet ·)` alone (the
   seam/slice separation and the ends clause need no extra hypothesis);
2. `Work.Drive.cntAt_pair_eq_one_of_threeBlockT6` (`Drive/hn2Reference`) — the parity algebra turning
   the three block multiplicativities T6, the vanishing of the reference block's factors and the
   oddness of the mixed factors into the two-term identity between the germ's own counts `CntAt`;
3. `Work.Drive.sideGerm_add_neg_eq_one_of_counts_at_levels` (`Drive/hn2CountInterface`) — the dictionary
   from the count identity at the **truncation levels** to the **germ** antisymmetry at the design's
   level;

into the statement the wall consumes:

> **`Work.Drive.sideGerm_add_neg_eq_one_of_refTripleEngine`** —
> `sideGerm Ξ Q c a + sideGerm Ξ Q c (-a) = 1`.

The remaining hypotheses are exactly the four outputs of the other lanes:

* `hmeet` — the Sard genericity of the perturbed reference triple
  (`Work.Drive.exists_meet3Hyp_sweepChartFam_of_locus`; its residual input is the chart containment
  `hloc`, cf. `Drive/refTripleHloc.lean`) together with `hodd`, the class-triple parity
  (`Work.Drive.odd_ncard_classTripleSet_of_hasClassLinearization`, the linearization lane);
* `hblock` — the transport's multiplicativity T6 at the three blocks of the reference triple
  (`Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design_avoidance` and its companions);
* `h20`, `h21` — the vanishing of the reference block's own factors (`(F2)`,
  `Work.Drive.not_odd_coreSideCount_reference_perturbed`, proved);
* `h02`, `h12` — the oddness of the two mixed factors (`(F1)`,
  `Work.Drive.exists_delta_odd_coreSideCountPt_mixed` / `odd_coreSideCountPt_reference_mixed`, proved);
* `hg01`, `hg10` — the identification of the two configuration factors with the germ counts
  (`Work.Drive.coreSideCount_block_eq_CntAt`, proved);
* the germ lane's locality data (`hUa`, `hUa'`, `hparA`, `hUn`, `hUn'`, `hparN`) and the two
  pair-goodness facts at the coupled parameter, which the reference-triple genericity supplies at the
  same `t` as `hmeet`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **`hn2` at one angle, end to end, from the reference-triple data.** -/
theorem sideGerm_add_neg_eq_one_of_refTripleEngine
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace)
    (hΞ : ChartPert Q 4 Ξ) (hQ : IsSmoothChart Q) (c : ℝ) (hc : 0 < c)
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) (a : UnitAddCircle)
    (t : EuclideanSpace ℝ (Fin 12)) (cblk : Fin 3 → ℝ) (g : Fin 3 → Fin 3 → ℕ)
    (hg01 : g 0 1 = CntAt Ξ Q (cblk 1) a (blk 0 t, blk 1 t))
    (hg10 : g 1 0 = CntAt Ξ Q (cblk 0) (-a) (blk 1 t, blk 0 t))
    (hcpos : ∀ k : Fin 3, 0 < cblk k)
    (hc1 : cblk 1 < cblk 0) (hc2 : cblk 2 < cblk 0)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      cblk 0 < levelOf ((fun z => Ξ (blk k t) (P k z)) y))
    (hmeet : Meet3Hyp CappingSpace (sweepChartFam P Ξ cblk t))
    (hodd : Odd (classTripleSet (fun k => fun z => Ξ (blk k t) (P k z))).ncard)
    (hblock : ∀ k : Fin 3,
      Odd ((topBdryMeet CappingSpace (sweepChartFam P Ξ cblk t) k).ncard) ↔
        (Odd (g k (k + 1)) ∧ Odd (g k (k + 2))))
    (h20 : Even (g 2 0)) (h21 : Even (g 2 1)) (h02 : Odd (g 0 2)) (h12 : Odd (g 1 2))
    {ε : ℝ} (hε : 0 < ε)
    (hUa : ∀ s s' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖s‖ < ε → ‖s'‖ < ε → GoodAt Ξ Q c a s → GoodAt Ξ Q c a s' →
        Odd (CntAt Ξ Q c a s) = Odd (CntAt Ξ Q c a s'))
    (hUa' : ∀ s s' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖s‖ < ε → ‖s'‖ < ε → GoodAt Ξ Q (cblk 1) a s → GoodAt Ξ Q (cblk 1) a s' →
        Odd (CntAt Ξ Q (cblk 1) a s) = Odd (CntAt Ξ Q (cblk 1) a s'))
    (hparA : ∀ s : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      GoodAt Ξ Q c a s → GoodAt Ξ Q (cblk 1) a s →
        Odd (CntAt Ξ Q c a s) = Odd (CntAt Ξ Q (cblk 1) a s))
    (hUn : ∀ s s' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖s‖ < ε → ‖s'‖ < ε → GoodAt Ξ Q c (-a) s → GoodAt Ξ Q c (-a) s' →
        Odd (CntAt Ξ Q c (-a) s) = Odd (CntAt Ξ Q c (-a) s'))
    (hUn' : ∀ s s' : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      ‖s‖ < ε → ‖s'‖ < ε → GoodAt Ξ Q (cblk 0) (-a) s → GoodAt Ξ Q (cblk 0) (-a) s' →
        Odd (CntAt Ξ Q (cblk 0) (-a) s) = Odd (CntAt Ξ Q (cblk 0) (-a) s'))
    (hparN : ∀ s : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4),
      GoodAt Ξ Q c (-a) s → GoodAt Ξ Q (cblk 0) (-a) s →
        Odd (CntAt Ξ Q c (-a) s) = Odd (CntAt Ξ Q (cblk 0) (-a) s))
    (ht : ‖(blk 0 t, blk 1 t)‖ < ε) (ht' : ‖(blk 1 t, blk 0 t)‖ < ε)
    (hgood01 : GoodAt Ξ Q (cblk 1) a (blk 0 t, blk 1 t))
    (hgood10 : GoodAt Ξ Q (cblk 0) (-a) (blk 1 t, blk 0 t)) :
    sideGerm Ξ Q c a + sideGerm Ξ Q c (-a) = 1 := by
  have htop := odd_sum_topBdryMeet_sweepChartFam P Ξ cblk t hcpos hc1 hc2 hlev hmeet hodd
  have hkey := cntAt_pair_eq_one_of_threeBlockT6 Ξ Q ![0, a, 0] (fun k => blk k t) cblk
    (fun k => (topBdryMeet CappingSpace (sweepChartFam P Ξ cblk t) k).ncard) g
    (by simpa using hg01) (by simpa using hg10) htop hblock h20 h21 h02 h12
  have hkey' : ((CntAt Ξ Q (cblk 1) a (blk 0 t, blk 1 t) : ℕ) : ZMod 2)
      + ((CntAt Ξ Q (cblk 0) (-a) (blk 1 t, blk 0 t) : ℕ) : ZMod 2) = 1 := by
    simpa using hkey
  exact sideGerm_add_neg_eq_one_of_counts_at_levels Ξ Q hΞ hQ c (cblk 1) (cblk 0)
    hc (hcpos 1) (hcpos 0) a hε hUa hUa' hparA hUn hUn' hparN
    ht ht' hgood01 hgood10 hkey'

end

end Work.Drive
