import Mathlib
import Submission.Work.Drive.endTripleRegUnrestricted
import Submission.Work.Drive.refTripleProducerDefs

/-!
# The reference triple's end data: `EndTripleReg` of the three perturbed block planes

The `hn2` node (`Work.Drive.hn2_refTripleAt_producer`) needs, for its class-triple parity
(`refTripleAt_classOdd_at`) and hence for `Work.Drive.hasClassLinearization_of_endData`, the
**class-level end data** of its own triple of perturbed planes
`refBlock Ξ Q (refPlanePres φ lam hlam) u v t k` (`k = 0,1,2`).

Its hypotheses supply the two inputs of the producer: the level bound (`hlev`) and the sweeps'
`Meet3Hyp` (`hmeet`, i.e. `Meet3Hyp` of `sweepChartFam (refTriple …) Ξ cblk t`).  What is *also* needed
is the **affine invariance** of each block:
`refTriple Q (refPlanePres φ lam hlam) u v k` is a `diskPlane` presentation
(`rotPresentation Q w = diskPlane (rotCapping w ∘ Q)` and
`refPlanePres φ lam hlam = diskPlane (linPlaneChart (φ 2) lam hlam)`), so each of its blocks is
invariant under the lattice/reflection symmetries `x ↦ (ε i * x i + 2 m i)` of the parameter square —
which is what `Work.Drive.endTripleReg_of_meet3Hyp_sweeps_unrestricted` consumes.

This file supplies:

* `Work.Drive.refTriple_affRep`, `Work.Drive.refBlock_affRep` — the invariance;
* `Work.Drive.refBlock_contMDiff` — the smoothness of the blocks;
* `Work.Drive.endTripleReg_refBlock_of_meet3Hyp` — **the end data `EndTripleReg` of the reference
  triple's blocks**, over *all* of `ℝ²` (row 1 of `NOTES_LEAD_hodd_blockT6.md` §3, without the
  box-residency hypothesis).
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace
attribute [local instance] Work.Drive.projCharted
local instance instIsManifoldProjChartR :
    IsManifold (𝓡 3) Work.Drive.Ctop (Projectivization ℝ (Eucl 3)) :=
  Work.Drive.isManifold_projCharted 3

/-! ## 1. The invariance of the reference triple under the affine symmetries -/

/-- **The reference plane's presentation is a `diskPlane` presentation.** -/
lemma refPlanePres_eq_diskPlane (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam) :
    refPlanePres φ lam hlam = diskPlane (linPlaneChart (φ 2) lam hlam) := rfl

/-- **The blocks of the reference triple are invariant under the affine symmetries of the parameter
square.**  Each block is `rotPresentation Q u = diskPlane (rotCapping u ∘ Q)`,
`rotPresentation Q v`, or the reference plane's `diskPlane` presentation, and `diskPlane` is
`foldBox`-based (`Work.Drive.diskPlane_affRep`). -/
lemma refTriple_affRep (Q : ℂ → CappingSpace) (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ)
    (hlam : 0 < lam) (u v : UnitAddCircle) {e : Fin 2 → ℝ} (he : ∀ i, e i = 1 ∨ e i = -1)
    (mm : Fin 2 → ℤ) (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)) :
    refTriple Q (refPlanePres φ lam hlam) u v k (affRep e mm y)
      = refTriple Q (refPlanePres φ lam hlam) u v k y := by
  fin_cases k
  · simpa [refTriple] using rotPresentation_affRep he mm Q u y
  · simpa [refTriple] using rotPresentation_affRep he mm Q v y
  · simpa [refTriple, refPlanePres_eq_diskPlane] using
      diskPlane_affRep he mm (linPlaneChart (φ 2) lam hlam) y

/-- **The blocks of the perturbed reference triple are invariant** — the `hinv` input of the
unrestricted producer. -/
lemma refBlock_affRep (Ξ : Eucl 3 → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam) (u v : UnitAddCircle)
    (t : EuclideanSpace ℝ (Fin 12)) {e : Fin 2 → ℝ} (he : ∀ i, e i = 1 ∨ e i = -1)
    (mm : Fin 2 → ℤ) (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)) :
    refBlock Ξ Q (refPlanePres φ lam hlam) u v t k (affRep e mm y)
      = refBlock Ξ Q (refPlanePres φ lam hlam) u v t k y := by
  simp only [refBlock, refTriple_affRep Q φ lam hlam u v he mm k y]

/-! ## 2. The smoothness of the perturbed blocks -/

/-- **The perturbed blocks of the reference triple are `C^∞`**, from the joint smoothness of the
perturbation family and the smoothness of the reference triple. -/
lemma refBlock_contMDiff (Q : ℂ → CappingSpace) (hQsm : IsSmoothChart Q)
    (Ξ : Eucl 3 → CappingSpace → CappingSpace) (hΞ : ChartPert Q 4 Ξ)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam) (u v : UnitAddCircle)
    (t : EuclideanSpace ℝ (Fin 12)) :
    ∀ k : Fin 3, ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop
      (refBlock Ξ Q (refPlanePres φ lam hlam) u v t k) := by
  have hΞsm : ∀ s : Eucl 3, ContMDiff (𝓡 4) (𝓡 4) Work.Drive.Ctop
      (fun p : CappingSpace => Ξ s p) := fun s =>
    hΞ.2.1.comp (contMDiff_const.prodMk contMDiff_id)
  intro k
  exact (hΞsm (blk k t)).comp (refTriple_contMDiff Q hQsm φ lam hlam u v k)

/-! ## 3. The end data -/

/-- **Row 1 of the ends clause at the `hn2` node's own reference triple**: the class-level end data
`Work.Drive.EndTripleReg` of the three perturbed block planes, over **all** of `ℝ²`, from the node's
own hypotheses (the level bound and the sweeps' `Meet3Hyp`).

The affine invariance is `Work.Drive.refBlock_affRep` (§1); the producer is
`Work.Drive.endTripleReg_of_meet3Hyp_sweeps_unrestricted`. -/
theorem endTripleReg_refBlock_of_meet3Hyp
    (Q : ℂ → CappingSpace) (hQsm : IsSmoothChart Q)
    (Ξ : Eucl 3 → CappingSpace → CappingSpace) (hΞ : ChartPert Q 4 Ξ)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (u v : UnitAddCircle) (cblk : Fin 3 → ℝ) (t : EuclideanSpace ℝ (Fin 12))
    (hcpos : ∀ k, 0 < cblk k) (hc10 : cblk 1 < cblk 0) (hc20 : cblk 2 < cblk 0)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      cblk 0 < levelOf (refBlock Ξ Q (refPlanePres φ lam hlam) u v t k y))
    (hmeet : Meet3Hyp CappingSpace
      (sweepChartFam (refTriple Q (refPlanePres φ lam hlam) u v) Ξ cblk t)) :
    Work.Drive.EndTripleReg (Work.Drive.planeClassMap
        (refBlock Ξ Q (refPlanePres φ lam hlam) u v t 0))
      (Work.Drive.planeClassMap (refBlock Ξ Q (refPlanePres φ lam hlam) u v t 1))
      (Work.Drive.planeClassMap (refBlock Ξ Q (refPlanePres φ lam hlam) u v t 2)) := by
  have hmeet' : Meet3Hyp CappingSpace
      (fun k => clampedSweep (cblk k) (fun s : ℝ => 1 - s)
        (refBlock Ξ Q (refPlanePres φ lam hlam) u v t k)) := by
    rw [← sweepChartFam_eq_refBlock Ξ Q (refPlanePres φ lam hlam) u v cblk t]
    exact hmeet
  exact endTripleReg_of_meet3Hyp_sweeps_unrestricted cblk (fun s : ℝ => 1 - s)
    (fun k => refBlock Ξ Q (refPlanePres φ lam hlam) u v t k) contDiff_designCutoff
    (refBlock_contMDiff Q hQsm Ξ hΞ φ lam hlam u v t) hcpos hc10 hc20
    (by norm_num) (by norm_num) continuousOn_designCutoff strictAntiOn_designCutoff
    (fun e mm he k y => refBlock_affRep Ξ Q φ lam hlam u v t he mm k y) hlev hmeet'

end

end Work.Drive
