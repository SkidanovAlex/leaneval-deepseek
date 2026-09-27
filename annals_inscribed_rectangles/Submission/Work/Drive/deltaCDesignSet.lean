import Mathlib
import Submission.Work.Drive.deltaCDesign
import Submission.Work.Drive.forallNeOpen
import Submission.Work.Drive.chartShiftHsurj
import Submission.Work.Drive.sweepTripleGeneric

/-!
# The design's cut-avoidance condition as an *open* condition in the parameter

`Work.Drive.exists_deltaC_design` (`Submission/Work/Drive/deltaCDesign.lean`) produces the third
conjunct of `Work.Drive.T6GenAt` at the design's block `k` for parameters `σ` of the block `k` of an
arbitrarily close parameter family.  This file packages the conjunct as a *set of parameters*

> `Work.Drive.DesignCutAvoids Q u cblk k t`  (the `δc` conjunct of `T6GenAt` at the parameter `t`),

and proves it **open** in `t`, which is what the design's joint genericity interface
(`Work.Drive.exists_meet3Hyp_rot_local_of_openDense`, whose `Pcond` arguments are open sets dense at
every point of the unit ball) consumes.  The density at every point is
`Work.Drive.exists_deltaC_design` (a move of the block `k` parameter alone); the openness is the
closedness of the coincidence set of the two continuous families `(t, x) ↦ sweep_t x` and
`t ↦ chart_t 0`, via `Work.Drive.isOpen_setOf_forall_ne_of_isCompact` (the projection `X × K → X` is
closed for `K` compact).
-/

namespace Work.Drive

open scoped Topology Manifold ContDiff
open Filter Set

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 1000000

/-- **The design's cut-avoidance condition at the parameter `t`**: the third conjunct of
`Work.Drive.T6GenAt` (`∃ δc > 0`, cut of the block-`k` chart against the sweep of the block-`k+2`
plane) at the design's parameter family `t ↦ fun j => blk j t`. -/
def DesignCutAvoids {Q : ℂ → CappingSpace} (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ)
    (k : Fin 3) (t : EuclideanSpace ℝ (Fin 12)) : Prop :=
  ∃ δc : ℝ, 0 < δc ∧ ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δc →
    x ∉ diskCut (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k)
      (designSweep (fun s p => chartPert s p) Q u (fun j => blk j t) cblk (k + 2))

/-- **The design's cut-avoidance condition is open in the design parameter.** -/
theorem isOpen_designCutAvoids {Q : ℂ → CappingSpace} (hQ : IsChartData Q)
    (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ) (k : Fin 3) :
    IsOpen {t : EuclideanSpace ℝ (Fin 12) | DesignCutAvoids (Q := Q) u cblk k t} := by
  have hΞ : ChartPert Q 4 (fun s p => chartPert s p) :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  let P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace := fun j => rotPresentation Q (u j)
  have hP : ∀ j : Fin 3, ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (P j) :=
    fun j => contMDiff_rotPresentation Q (u j) (contMDiff_diskPlane (Q := Q) hQ.1)
  -- joint continuity of the two families
  have hblockPlane : ∀ q : EuclideanSpace ℝ (Fin 12),
      blockPlane (fun s p => chartPert s p) Q u (fun j => blk j q) (k + 2)
        = fun z => chartPert (blk (k + 2) q) (rotPresentation Q (u (k + 2)) z) :=
    fun q => rfl
  have hScont : Continuous (Function.uncurry (fun (t : EuclideanSpace ℝ (Fin 12))
      (x : EuclideanSpace ℝ (Fin 3)) =>
      designSweep (fun s p => chartPert s p) Q u (fun j => blk j t) cblk (k + 2) x)) := by
    have hslice := fun j : Fin 3 => contMDiff_sweepChartSlice_of_family hΞ hP cblk j
    have hGsm := (contMDiff_sweepChartFam P (fun s p => chartPert s p) cblk hslice (k + 2)).continuous
    have heq : Function.uncurry (fun (t : EuclideanSpace ℝ (Fin 12))
          (x : EuclideanSpace ℝ (Fin 3)) =>
          designSweep (fun s p => chartPert s p) Q u (fun j => blk j t) cblk (k + 2) x)
        = (fun q : EuclideanSpace ℝ (Fin 12) × EuclideanSpace ℝ (Fin 3) =>
            sweepChartFam P (fun s p => chartPert s p) cblk q.1 (k + 2) q.2) := by
      funext q
      simp only [Function.uncurry, designSweep, sweepChartFam, P, hblockPlane,
        Function.comp_apply]
    rw [heq]
    exact hGsm
  have hTcont : Continuous (fun t : EuclideanSpace ℝ (Fin 12) =>
      blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k 0) := by
    have hjoint := contMDiff_chartPert.continuous
    have hlin : Continuous fun t : EuclideanSpace ℝ (Fin 12) =>
        ((blk k t, rotCapping (u k) (Q 0)) : EuclideanSpace ℝ (Fin 4) × CappingSpace) :=
      ((blk k).continuous).prodMk continuous_const
    have hfun : (fun t : EuclideanSpace ℝ (Fin 12) =>
          blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k 0)
        = (fun q : EuclideanSpace ℝ (Fin 4) × CappingSpace => chartPert q.1 q.2) ∘
          fun t : EuclideanSpace ℝ (Fin 12) => (blk k t, rotCapping (u k) (Q 0)) := by
      funext t
      simp only [blockChart, Function.comp_apply]
    rw [hfun]
    exact hjoint.comp hlin
  -- the pointwise identification with the "no coincidence on the box" condition
  have hiff : ∀ t : EuclideanSpace ℝ (Fin 12), DesignCutAvoids (Q := Q) u cblk k t ↔
      ∀ x ∈ Submission.Drive.unitBox 2,
        designSweep (fun s p => chartPert s p) Q u (fun j => blk j t) cblk (k + 2) x
          ≠ blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k 0 := by
    intro t
    rw [DesignCutAvoids]
    have hcont1 : Continuous (blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k) := by
      have hjoint := contMDiff_chartPert.continuous
      have hlin : Continuous fun z : ℂ =>
          ((blk k t, rotCapping (u k) (Q z)) : EuclideanSpace ℝ (Fin 4) × CappingSpace) :=
        continuous_const.prodMk ((continuous_rotCapping (u k)).comp hQ.1.continuous)
      have hfun : blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k
          = (fun q : EuclideanSpace ℝ (Fin 4) × CappingSpace => chartPert q.1 q.2) ∘
            (fun z : ℂ => (blk k t, rotCapping (u k) (Q z))) := by
        funext z
        simp only [blockChart, Function.comp_apply]
      rw [hfun]
      exact hjoint.comp hlin
    have hcont2 : Continuous (designSweep (fun s p => chartPert s p) Q u (fun j => blk j t)
        cblk (k + 2)) := by
      have h : Continuous (fun x : EuclideanSpace ℝ (Fin 3) =>
          Function.uncurry (fun (t : EuclideanSpace ℝ (Fin 12))
            (x : EuclideanSpace ℝ (Fin 3)) =>
            designSweep (fun s p => chartPert s p) Q u (fun j => blk j t) cblk (k + 2) x) (t, x)) :=
        hScont.comp (continuous_const.prodMk continuous_id)
      simpa only [Function.uncurry] using h
    rw [exists_deltaC_iff_notMem _ _ hcont1 hcont2]
    constructor
    · intro h x hx heq
      exact h ⟨x, hx, heq⟩
    · rintro h ⟨x, hx, heq⟩
      exact h x hx heq
  rw [show {t : EuclideanSpace ℝ (Fin 12) | DesignCutAvoids (Q := Q) u cblk k t}
      = {t : EuclideanSpace ℝ (Fin 12) | ∀ x ∈ Submission.Drive.unitBox 2,
          designSweep (fun s p => chartPert s p) Q u (fun j => blk j t) cblk (k + 2) x
            ≠ blockChart (fun s p => chartPert s p) Q u (fun j => blk j t) k 0}
      from Set.ext fun t => hiff t]
  exact isOpen_setOf_forall_ne_of_isCompact (isCompact_unitBox 2) hScont hTcont

end

end Work.Drive
