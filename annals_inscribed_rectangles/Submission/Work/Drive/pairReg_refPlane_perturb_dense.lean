import Mathlib
import Submission.Work.Drive.sgGoodChain_of_small_shift_sweep
import Submission.Work.Drive.boxThree_of_good_family
import Submission.Work.Drive.pairReg_of_loopBoxData
import Submission.Work.Drive.unrestrictedFromBox
import Submission.Work.Drive.boxThreeDefs
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.refTripleProducerDefs
import Submission.Work.Drive.linearPlaneChart
import Submission.Work.Drive.planeChain
import Submission.Work.Drive.sideValue
import Submission.Work.Drive.rotCappingSmooth
import Submission.Work.Drive.exists_loopBoxData_of_small_shift_fam
import Submission.Work.Drive.pairRegRows
import Submission.Work.Drive.classProjectionBricks
import Submission.Work.Drive.blockPlaneInvariant
import Submission.Work.Drive.contMDiff_rotPresentation
import Submission.Work.Drive.blockVocabulary

/-!
# The pair row `PairReg P̂₁ P̂₂` of the reference triple, at arbitrarily small perturbations of the
reference plane

`Work.Drive.pairReg_refPlane_perturb_dense`: for the *fixed* perturbed rotated chart
`A = chartPert τ₁ ∘ rotPresentation Q v` of the curve's chart and the *linear reference plane*
`refPlanePres φ lam hlam`, there are perturbations `σ` of the reference block's chart parameter,
arbitrarily small and keeping the level `(ρ + σ) 0` positive, such that the two class maps are
`Work.Drive.PairReg`:

> at every common value of `planeClassMap A` and `planeClassMap (chartPert (ρ+σ) ∘ refPlanePres …)`
> the two class derivative ranges span the tangent space `T ℝP³`.

## The route (no new geometry: the workspace's parametric Sard)

`Work.Drive.pairReg_of_loopBoxData_affRep` produces `PairReg` from the box data
`LoopBoxData (shadow lam hlam ∘ A) (clampedSweep c₂ ψ P_σ)` of the *shadow of the loop* `A` on the
level `lam`.  That box data is produced by the multi-family parametric Sard
`Work.Drive.boxThree_of_good_family`, in its packaged form
`Work.Drive.exists_loopBoxData_of_small_shift_fam`: *for any finite family of smooth loops whose
values on the square lie in the levels `> c`, there is an arbitrarily small perturbation of the
chain's chart parameter at which the box data holds against the clamped sweep of that perturbed
chart*.  Instantiating at the single loop `shadow lam hlam ∘ A`, the chain chart
`Q₀ = linPlaneChart (φ 2) lam hlam` (whose disk presentation is `refPlanePres φ lam hlam`) and the
perturbation family `chartPert`, the produced sweep is

> `clampedSweep c₂ (1 - ·) (diskPlane (pertChart chartPert Q₀ (ρ + σ)))`
>   `= clampedSweep c₂ (1 - ·) (chartPert (ρ + σ) ∘ refPlanePres φ lam hlam)`,

which is exactly the second presentation of the pair row.  The two analytic hypotheses of the Sard
(smoothness of the chain family, surjectivity of its charted parameter-derivative at meets) are
supplied by `Work.Drive.contMDiff_sggSweepFam` and `Work.Drive.hsurj_sggSweepFam`; the latter uses
the level band `c₂ < lam` of the loop to exclude the radial faces of the sweep, and the level bound
`lam < levelOf (chartPert (ρ+σ) (refPlanePres … y))` needed by the pair bridge is exactly the
positivity `0 < (ρ + σ) 0` of the conclusion.
-/

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace
attribute [local instance] Work.Drive.projCharted
local instance instIsManifoldProjChartPRD :
    IsManifold (𝓡 3) Work.Drive.Ctop (Projectivization ℝ (Eucl 3)) :=
  Work.Drive.isManifold_projCharted 3

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

theorem pairReg_refPlane_perturb_dense
    {Q : ℂ → CappingSpace} (hQ : IsSmoothChart Q) (v : UnitAddCircle)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (τ₁ ρ : Eucl 3) (hρ : 0 < ρ 0) (c₂ : ℝ) (hc₂ : 0 < c₂) (hcl : c₂ < lam)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ σ : Eucl 3, ‖σ‖ < ε ∧ 0 < (ρ + σ) 0 ∧
      PairReg (planeClassMap (fun y => chartPert τ₁ (rotPresentation Q v y)))
        (planeClassMap (fun y => chartPert (ρ + σ) (refPlanePres φ lam hlam y))) := by
  classical
  -- the chart-perturbation family of the capping space and the linear reference chart
  have hΞ : ChartPert (linPlaneChart (φ 2) lam hlam) 4 (fun s p => chartPert s p) :=
    isChartPert_chartPert _
  have hQ0 : IsSmoothChart (linPlaneChart (φ 2) lam hlam) :=
    linPlaneChart_contMDiff (φ 2) lam hlam
  -- smoothness of the perturbed rotated chart, and of its shadow on the level `lam`
  have hτ₁sm : ContMDiff (𝓡 4) (𝓡 4) Ctop (fun p : CappingSpace => chartPert τ₁ p) :=
    contMDiff_apply_of_chartPert hΞ τ₁
  have hrotsm : ContMDiff (𝓡 2) (𝓡 4) Ctop (rotPresentation Q v) :=
    contMDiff_rotPresentation Q v (contMDiff_diskPlane hQ)
  have hLsm : SmoothPlane₂ (fun y : EuclideanSpace ℝ (Fin 2) =>
      shadow lam hlam (chartPert τ₁ (rotPresentation Q v y))) :=
    (contMDiff_shadow lam hlam).comp (hτ₁sm.comp hrotsm)
  -- the level band of the loop
  have hLlev : ∀ (i : Unit) (u : EuclideanSpace ℝ (Fin 2)),
      u ∈ Submission.Drive.unitBox 1 →
        c₂ < levelOf (shadow lam hlam (chartPert τ₁ (rotPresentation Q v u))) := by
    intro i u hu
    rw [levelOf_shadow]
    exact hcl
  -- the parametric Sard: move the plane block's chart parameter only
  obtain ⟨σ, hσ, hbox⟩ := exists_loopBoxData_of_small_shift_fam (m := 4) (ι := Unit)
    (fun _ : Unit => fun y : EuclideanSpace ℝ (Fin 2) =>
      shadow lam hlam (chartPert τ₁ (rotPresentation Q v y)))
    (fun _ => hLsm) c₂ hc₂ hLlev (fun s p => chartPert s p)
    (linPlaneChart (φ 2) lam hlam) hΞ hQ0 (0 : UnitAddCircle) ρ
    (min (ε / 2) (ρ 0 / 2)) (lt_min (by linarith) (by linarith))
  -- the two size bounds and the positivity of the perturbed level
  have hσlt : ‖σ‖ < ε :=
    lt_of_lt_of_le hσ (le_trans (min_le_left _ _) (by linarith))
  have hσrho : ‖σ‖ < ρ 0 / 2 := lt_of_lt_of_le hσ (min_le_right _ _)
  have hposρσ : 0 < (ρ + σ) 0 := by
    have h1 : |σ 0| ≤ ‖σ‖ := by
      rw [← Real.norm_eq_abs]
      exact PiLp.norm_apply_le σ (0 : Fin 4)
    have h2 : (ρ + σ) 0 = ρ 0 + σ 0 := by simp
    rw [h2]
    linarith [neg_abs_le (σ 0)]
  refine ⟨σ, hσlt, hposρσ, ?_⟩
  -- the box data in the shape the pair bridge consumes
  have hbox' : LoopBoxData
      (fun u : EuclideanSpace ℝ (Fin 2) =>
        shadow lam hlam (chartPert τ₁ (rotPresentation Q v u)))
      (clampedSweep c₂ (fun s : ℝ => 1 - s)
        (fun y : EuclideanSpace ℝ (Fin 2) =>
          chartPert (ρ + σ) (refPlanePres φ lam hlam y))) := by
    have h := hbox ()
    have hrot : (fun z : ℂ => rotCapping (0 : UnitAddCircle)
          ((linPlaneChart (φ 2) lam hlam) z))
        = fun z : ℂ => (linPlaneChart (φ 2) lam hlam) z := by
      funext z
      simp only [rotCapping_zero, id_eq]
    have hchart : pertChart (fun s p => chartPert s p)
          (fun z : ℂ => rotCapping (0 : UnitAddCircle) ((linPlaneChart (φ 2) lam hlam) z))
          (ρ + σ)
        = fun z : ℂ => chartPert (ρ + σ) ((linPlaneChart (φ 2) lam hlam) z) := by
      rw [hrot]
      rfl
    rw [hchart] at h
    have hdisk : diskPlane (fun z : ℂ => chartPert (ρ + σ)
          ((linPlaneChart (φ 2) lam hlam) z))
        = fun y : EuclideanSpace ℝ (Fin 2) =>
            chartPert (ρ + σ) (refPlanePres φ lam hlam y) := by
      funext y
      rfl
    rw [hdisk] at h
    exact h
  -- the pair bridge
  refine pairReg_of_loopBoxData_affRep
    (fun y : EuclideanSpace ℝ (Fin 2) => chartPert τ₁ (rotPresentation Q v y))
    (fun y : EuclideanSpace ℝ (Fin 2) => chartPert (ρ + σ) (refPlanePres φ lam hlam y))
    (hτ₁sm.comp hrotsm) ?_ ?_ ?_ c₂ hc₂ lam hlam hcl (fun s : ℝ => 1 - s)
    (by norm_num) (by norm_num) continuousOn_designCutoff strictAntiOn_designCutoff ?_ hbox'
  · -- smoothness of the perturbed reference plane
    exact (contMDiff_apply_of_chartPert hΞ (ρ + σ)).comp (refPlanePres_contMDiff φ lam hlam)
  · -- affine invariance of the perturbed rotated chart
    intro e mm he y
    show chartPert τ₁ (rotPresentation Q v (affRep e mm y))
      = chartPert τ₁ (rotPresentation Q v y)
    rw [rotPresentation_affRep he mm Q v y]
  · -- affine invariance of the perturbed reference plane
    intro e mm he y
    show chartPert (ρ + σ) (refPlanePres φ lam hlam (affRep e mm y))
      = chartPert (ρ + σ) (refPlanePres φ lam hlam y)
    have h := diskPlane_affRep he mm (linPlaneChart (φ 2) lam hlam) y
    simp only [refPlanePres] at h ⊢
    rw [h]
  · -- the level of the perturbed reference plane is strictly above `lam`
    intro y
    show lam < levelOf (chartPert (ρ + σ) (refPlanePres φ lam hlam y))
    rw [levelOf_chartPert_mul, refPlanePres_level]
    have hexp : 1 < Real.exp ((ρ + σ).ofLp 0) := by
      refine Real.one_lt_exp_iff.mpr ?_
      have h0 : (ρ + σ).ofLp 0 = (ρ + σ) 0 := rfl
      rw [h0]
      exact hposρσ
    calc lam = lam * 1 := (mul_one lam).symm
      _ < lam * Real.exp ((ρ + σ).ofLp 0) := mul_lt_mul_of_pos_left hexp hlam

end

end Work.Drive
