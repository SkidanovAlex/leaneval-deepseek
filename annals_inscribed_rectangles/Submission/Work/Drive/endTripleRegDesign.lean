import Mathlib
import Submission.Work.Drive.endTripleRegOfMeet3
import Submission.Work.Drive.blockVocabulary
import Submission.Work.Drive.perturbedTripleIdentity

/-!
# The row-1/row-2 producer at the design's concrete triple

`Work.Drive.endTripleReg_of_meet3Hyp_sweeps` is stated for abstract plane presentations.  This file
instantiates it at the **design's** perturbed triple
(`Work.Drive.blockPlane Ξ Q u τ k`, `Work.Drive.designSweep Ξ Q u τ cblk` of
`Drive/perturbedTripleIdentity.lean`), with the cutoff `ψ = 1 - ·` of the design, so that the ends lane
can read the class-level end data `EndTripleReg` straight off its own `Meet3Hyp` (`DesignGoodData`'s
first conjunct) and level bound.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

noncomputable section

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace
attribute [local instance] Work.Drive.projCharted
local instance instIsManifoldProjChartD :
    IsManifold (𝓡 3) Work.Drive.Ctop (Projectivization ℝ (Eucl 3)) :=
  Work.Drive.isManifold_projCharted 3

lemma contDiff_designCutoff : ContDiff ℝ Work.Drive.Ctop (fun t : ℝ => 1 - t) := by
  fun_prop

lemma continuousOn_designCutoff : ContinuousOn (fun t : ℝ => 1 - t) (Set.Icc (0 : ℝ) 1) :=
  (continuous_const.sub continuous_id).continuousOn

lemma strictAntiOn_designCutoff : StrictAntiOn (fun t : ℝ => 1 - t) (Set.Icc (0 : ℝ) 1) := by
  intro a _ b _ hab
  simp only
  linarith

/-- **The design's row-1/row-2 producer**: the class-level end data of the three perturbed design
planes at every common-class triple of plane parameters in the closed unit square, from the design's
own `Meet3Hyp` of the three radial sweeps and its level bound. -/
theorem endTripleReg_blockPlane_of_designMeet3
    (Ξ : EuclideanSpace ℝ (Fin 4) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace)
    (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin 4)) (cblk : Fin 3 → ℝ)
    (hΞsm : ∀ s : EuclideanSpace ℝ (Fin 4),
      ContMDiff (𝓡 4) (𝓡 4) Work.Drive.Ctop (fun p : Work.Drive.CappingSpace => Ξ s p))
    (hQ : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop (Work.Drive.diskPlane Q))
    (hcpos : ∀ k, 0 < cblk k) (hc10 : cblk 1 < cblk 0) (hc20 : cblk 2 < cblk 0)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      cblk 0 < Work.Drive.levelOf (Work.Drive.blockPlane Ξ Q u τ k y))
    (hmeet : Meet3Hyp Work.Drive.CappingSpace (Work.Drive.designSweep Ξ Q u τ cblk)) :
    ∀ y : Fin 3 → EuclideanSpace ℝ (Fin 2),
      (∀ k, y k ∈ Submission.Drive.unitBox 1) →
      Work.Drive.CommonClass (fun k => Work.Drive.blockPlane Ξ Q u τ k) y →
      Function.Injective
        (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (Work.Drive.blockPlane Ξ Q u τ 0)) (y 0)) ∧
      Function.Injective
        (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (Work.Drive.blockPlane Ξ Q u τ 1)) (y 1)) ∧
      Function.Injective
        (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (Work.Drive.blockPlane Ξ Q u τ 2)) (y 2)) ∧
      ((mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (Work.Drive.blockPlane Ξ Q u τ 0))
            (y 0)).range ⊓
        (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (Work.Drive.blockPlane Ξ Q u τ 1))
            (y 1)).range ⊓
        (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap (Work.Drive.blockPlane Ξ Q u τ 2))
            (y 2)).range = ⊥) :=
  endTripleReg_of_meet3Hyp_sweeps cblk (fun t => 1 - t) (fun k => Work.Drive.blockPlane Ξ Q u τ k)
    contDiff_designCutoff (fun k => contMDiff_blockPlane Ξ hΞsm Q u τ k hQ) hcpos hc10 hc20
    (by norm_num) (by norm_num) continuousOn_designCutoff strictAntiOn_designCutoff hlev hmeet

end

end Work.Drive
