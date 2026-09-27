import Mathlib
import Submission.Work.Drive.pairReg_of_loopBoxData
import Submission.Work.Drive.unrestrictedFromBox
import Submission.Work.Drive.endTripleRegRefTriple
import Submission.Work.Drive.perturbedTripleIdentity

/-!
# The `PairReg` rows of the ends clause's class data

`Work.Drive.pairReg_of_loopBoxData` produces the *box-restricted* pair regularity
`Work.Drive.BoxPairReg` from a loop-versus-sweep meet regularity `Work.Drive.LoopBoxData`; the
consumers of the ends clause want the *unrestricted* `Work.Drive.PairReg`
(`Work.Drive.hasClassLinearization_of_endData`'s `hpair12`, `hpairL0P2`, `hpairL0L1`).

This file supplies the passage and its three instances at the design's presentations:

* `Work.Drive.pairReg_of_loopBoxData_affRep` — the generic passage, for presentations invariant under
  the affine symmetries of the parameter square (`Work.Drive.pairReg_of_boxPairReg_affRep`);
* `Work.Drive.pairReg_blockPlane_of_loopBoxData` — the design's perturbed rotated planes
  `blockPlane Ξ Q u τ k` (the `hpair12` input);
* `Work.Drive.pairReg_lin_blockPlane_of_loopBoxData` — a linear disk model
  `diskPlane (linPlaneChart (φ 0) c hc)` against a design block (the `hpairL0P2` input);
* `Work.Drive.pairReg_refBlock_of_loopBoxData` — the `hn2` node's reference blocks `refBlock …`.
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
local instance instIsManifoldProjChartPR :
    IsManifold (𝓡 3) Work.Drive.Ctop (Projectivization ℝ (Eucl 3)) :=
  Work.Drive.isManifold_projCharted 3

/-! ## 1. The generic passage -/

/-- **The unrestricted pair regularity from a loop-versus-sweep meet regularity**, for presentations
invariant under the affine symmetries of the parameter square. -/
theorem pairReg_of_loopBoxData_affRep
    (A P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hA : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop A)
    (hP : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop P)
    (hAinv : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2), A (affRep e mm y) = A y)
    (hPinv : ∀ (e : Fin 2 → ℝ) (mm : Fin 2 → ℤ), (∀ i, e i = 1 ∨ e i = -1) →
      ∀ y : EuclideanSpace ℝ (Fin 2), P (affRep e mm y) = P y)
    (c₂ : ℝ) (hc₂ : 0 < c₂) (lam : ℝ) (hlam : 0 < lam) (hcl : c₂ < lam)
    (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψcont : ContinuousOn ψ (Set.Icc 0 1)) (hψanti : StrictAntiOn ψ (Set.Icc 0 1))
    (hlevlam : ∀ y : EuclideanSpace ℝ (Fin 2), lam < Work.Drive.levelOf (P y))
    (hbox : Work.Drive.LoopBoxData (fun u => Work.Drive.shadow lam hlam (A u))
      (Work.Drive.clampedSweep c₂ ψ P)) :
    Work.Drive.PairReg (Work.Drive.planeClassMap A) (Work.Drive.planeClassMap P) :=
  pairReg_of_boxPairReg_affRep A P hA hP hAinv hPinv
    (pairReg_of_loopBoxData A P hA hP c₂ hc₂ lam hlam hcl ψ hψ0 hψ1 hψcont hψanti hlevlam hbox)

/-! ## 2. The design's rows -/

/-- **The `hpair12` row of the class data**: the pair regularity of two perturbed design blocks
(`blockPlane Ξ Q u τ k`, `blockPlane Ξ Q u τ j`) from the loop-versus-sweep regularity of the shadow
of the first against the radial sweep of the second. -/
theorem pairReg_blockPlane_of_loopBoxData
    (Ξ : EuclideanSpace ℝ (Fin 4) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace)
    (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin 4)) (k j : Fin 3)
    (hΞ : Work.Drive.ChartPert Q 4 Ξ) (hQ : Work.Drive.IsSmoothChart Q)
    (c₂ : ℝ) (hc₂ : 0 < c₂) (lam : ℝ) (hlam : 0 < lam) (hcl : c₂ < lam)
    (hlevlam : ∀ y : EuclideanSpace ℝ (Fin 2),
      lam < Work.Drive.levelOf (Work.Drive.blockPlane Ξ Q u τ j y))
    (hbox : Work.Drive.LoopBoxData (fun w => Work.Drive.shadow lam hlam
        (Work.Drive.blockPlane Ξ Q u τ k w))
      (Work.Drive.clampedSweep c₂ (fun s : ℝ => 1 - s) (Work.Drive.blockPlane Ξ Q u τ j))) :
    Work.Drive.PairReg (Work.Drive.planeClassMap (Work.Drive.blockPlane Ξ Q u τ k))
      (Work.Drive.planeClassMap (Work.Drive.blockPlane Ξ Q u τ j)) := by
  have hΞsm : ∀ s : EuclideanSpace ℝ (Fin 4), ContMDiff (𝓡 4) (𝓡 4) Work.Drive.Ctop
      (fun p : Work.Drive.CappingSpace => Ξ s p) := fun s =>
    hΞ.2.1.comp (contMDiff_const.prodMk contMDiff_id)
  exact pairReg_of_loopBoxData_affRep _ _
    (contMDiff_blockPlane Ξ hΞsm Q u τ k (contMDiff_diskPlane hQ)) (contMDiff_blockPlane Ξ hΞsm Q u τ j (contMDiff_diskPlane hQ))
    (fun e mm he _ => blockPlane_affRep he mm Ξ Q u τ k _)
    (fun e mm he _ => blockPlane_affRep he mm Ξ Q u τ j _)
    c₂ hc₂ lam hlam hcl (fun s : ℝ => 1 - s) (by norm_num) (by norm_num)
    continuousOn_designCutoff strictAntiOn_designCutoff hlevlam hbox

/-- **The `hpairL0P2` row of the class data**: the pair regularity of a linear disk model
`diskPlane (linPlaneChart (φ 0) c hc)` against a perturbed design block. -/
theorem pairReg_lin_blockPlane_of_loopBoxData
    (Ξ : EuclideanSpace ℝ (Fin 4) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin 4)) (j : Fin 3)
    (hΞ : Work.Drive.ChartPert Q 4 Ξ) (hQ : Work.Drive.IsSmoothChart Q)
    (c₂ : ℝ) (hc₂ : 0 < c₂) (lam : ℝ) (hlam : 0 < lam) (hcl : c₂ < lam)
    (hlevlam : ∀ y : EuclideanSpace ℝ (Fin 2),
      lam < Work.Drive.levelOf (Work.Drive.blockPlane Ξ Q u τ j y))
    (hbox : Work.Drive.LoopBoxData (fun w => Work.Drive.shadow lam hlam
        (Work.Drive.diskPlane (Work.Drive.linPlaneChart (φ 0) c hc) w))
      (Work.Drive.clampedSweep c₂ (fun s : ℝ => 1 - s) (Work.Drive.blockPlane Ξ Q u τ j))) :
    Work.Drive.PairReg
      (Work.Drive.planeClassMap (Work.Drive.diskPlane (Work.Drive.linPlaneChart (φ 0) c hc)))
      (Work.Drive.planeClassMap (Work.Drive.blockPlane Ξ Q u τ j)) := by
  have hΞsm : ∀ s : EuclideanSpace ℝ (Fin 4), ContMDiff (𝓡 4) (𝓡 4) Work.Drive.Ctop
      (fun p : Work.Drive.CappingSpace => Ξ s p) := fun s =>
    hΞ.2.1.comp (contMDiff_const.prodMk contMDiff_id)
  exact pairReg_of_loopBoxData_affRep _ _
    (Work.Drive.contMDiff_diskPlane (Work.Drive.linPlaneChart_contMDiff (φ 0) c hc))
    (contMDiff_blockPlane Ξ hΞsm Q u τ j (contMDiff_diskPlane hQ))
    (fun e mm he _ => diskPlane_affRep he mm _ _)
    (fun e mm he _ => blockPlane_affRep he mm Ξ Q u τ j _)
    c₂ hc₂ lam hlam hcl (fun s : ℝ => 1 - s) (by norm_num) (by norm_num)
    continuousOn_designCutoff strictAntiOn_designCutoff hlevlam hbox

/-- **The `hn2` node's pair row**: the pair regularity of two perturbed reference blocks
(`refBlock Ξ Q (refPlanePres φ lam₀ hlam₀) u v t 1`, `… t 2`) from the loop-versus-sweep regularity. -/
theorem pairReg_refBlock_of_loopBoxData
    (Ξ : Eucl 3 → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace) (hQsm : Work.Drive.IsSmoothChart Q)
    (hΞ : Work.Drive.ChartPert Q 4 Ξ)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam₀ : ℝ) (hlam₀ : 0 < lam₀)
    (u v : UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12)) (k j : Fin 3)
    (c₂ : ℝ) (hc₂ : 0 < c₂) (lam : ℝ) (hlam : 0 < lam) (hcl : c₂ < lam)
    (hlevlam : ∀ y : EuclideanSpace ℝ (Fin 2),
      lam < Work.Drive.levelOf (refBlock Ξ Q (refPlanePres φ lam₀ hlam₀) u v t j y))
    (hbox : Work.Drive.LoopBoxData (fun w => Work.Drive.shadow lam hlam
        (refBlock Ξ Q (refPlanePres φ lam₀ hlam₀) u v t k w))
      (Work.Drive.clampedSweep c₂ (fun s : ℝ => 1 - s)
        (refBlock Ξ Q (refPlanePres φ lam₀ hlam₀) u v t j))) :
    Work.Drive.PairReg
      (Work.Drive.planeClassMap (refBlock Ξ Q (refPlanePres φ lam₀ hlam₀) u v t k))
      (Work.Drive.planeClassMap (refBlock Ξ Q (refPlanePres φ lam₀ hlam₀) u v t j)) := by
  exact pairReg_of_loopBoxData_affRep _ _
    (refBlock_contMDiff Q hQsm Ξ hΞ φ lam₀ hlam₀ u v t k)
    (refBlock_contMDiff Q hQsm Ξ hΞ φ lam₀ hlam₀ u v t j)
    (fun e mm he _ => refBlock_affRep Ξ Q φ lam₀ hlam₀ u v t he mm k _)
    (fun e mm he _ => refBlock_affRep Ξ Q φ lam₀ hlam₀ u v t he mm j _)
    c₂ hc₂ lam hlam hcl (fun s : ℝ => 1 - s) (by norm_num) (by norm_num)
    continuousOn_designCutoff strictAntiOn_designCutoff hlevlam hbox

end

end Work.Drive
