import Mathlib
import Submission.Work.Drive.deltaCDesignSet
import Submission.Work.Drive.norm_blkSpan

/-!
# The design's cut-avoidance condition is *dense* in the design parameter

Together with `Work.Drive.isOpen_designCutAvoids` (`Submission/Work/Drive/deltaCDesignSet.lean`) this
makes the third conjunct of `Work.Drive.T6GenAt` an *open set dense at every point* of the design's
parameter space, i.e. an admissible `Pcond` of the joint genericity interface
`Work.Drive.exists_meet3Hyp_rot_local_of_openDense`.

The density is a one-block move: the sweep of the block `k+2` is held fixed and the block `k`
parameter is moved by `Work.Drive.exists_deltaC_shift` (whose empty-interior input is the weak-Sard
chapter, applied to the fixed sweep, a `C^∞` map `𝔼³ → CappingSpace`).  The parameter realising the
move is `t₀ + blkSpan k σ`: it has `‖t - t₀‖ = ‖σ‖` (`Work.Drive.norm_blkSpan`) and its block
projections are the moved one at `k` (`Work.Drive.blk_blkSpan`) and the original ones at `j ≠ k`
(`Work.Drive.blk_blkSpan_of_ne`).
-/

namespace Work.Drive

open scoped Topology Manifold ContDiff
open Filter Set

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 1000000

/-- Three is not two: the two distinguished blocks of the design are distinct. -/
private lemma fin3_add_two_ne (k : Fin 3) : (k + 2 : Fin 3) ≠ k := by
  fin_cases k <;> decide

/-- **The design's cut-avoidance condition holds at parameters arbitrarily close to any parameter.** -/
theorem exists_designCutAvoids_near {Q : ℂ → CappingSpace} (hQ : IsChartData Q)
    (u : Fin 3 → UnitAddCircle) (cblk : Fin 3 → ℝ) (k : Fin 3)
    (t₀ : EuclideanSpace ℝ (Fin 12)) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : EuclideanSpace ℝ (Fin 12), ‖t - t₀‖ < ε ∧ DesignCutAvoids (Q := Q) u cblk k t := by
  have hΞ : ChartPert Q 4 (fun s p => chartPert s p) :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  -- the sweep of the block `k + 2` at the base parameter, held fixed
  have hWsm : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (designSweep (fun s p => chartPert s p) Q u (fun j => blk j t₀) cblk (k + 2)) :=
    contMDiff_clampedSweep (cblk (k + 2)) (fun s => 1 - s)
      (blockPlane (fun s p => chartPert s p) Q u (fun j => blk j t₀) (k + 2)) (by fun_prop)
      (contMDiff_blockPlane (fun s p => chartPert s p)
        (fun s => contMDiff_apply_of_chartPert hΞ s) Q u (fun j => blk j t₀) (k + 2)
        (contMDiff_diskPlane (Q := Q) hQ.1))
  have hWint : interior ((designSweep (fun s p => chartPert s p) Q u (fun j => blk j t₀) cblk (k + 2))
      '' Submission.Drive.unitBox 2) = ∅ :=
    Sard.interior_image_eq_empty_of_contMDiff_of_lt (m := 3) (n := 4) (by norm_num) _ hWsm
      (Submission.Drive.unitBox 2)
  -- the move of the block `k` parameter
  obtain ⟨σ, hσ, hδ⟩ := exists_deltaC_shift (Ξ := fun s p => chartPert s p)
    (Q' := fun z : ℂ => rotCapping (u k) (Q z))
    ((continuous_rotCapping (u k)).comp hQ.1.continuous) hΞ
    (designSweep (fun s p => chartPert s p) Q u (fun j => blk j t₀) cblk (k + 2))
    hWsm.continuous hWint (blk k t₀) ε hε
  refine ⟨t₀ + blkSpan k σ, ?_, ?_⟩
  · rw [add_sub_cancel_left, norm_blkSpan]
    exact hσ
  · refine ⟨hδ.choose, hδ.choose_spec.1, ?_⟩
    intro x hx
    have hchart : blockChart (fun s p => chartPert s p) Q u
          (fun j => blk j (t₀ + blkSpan k σ)) k
        = fun z : ℂ => chartPert (blk k t₀ + σ) (rotCapping (u k) (Q z)) := by
      unfold blockChart
      simp only [map_add, blk_blkSpan]
    have hsweep : designSweep (fun s p => chartPert s p) Q u
          (fun j => blk j (t₀ + blkSpan k σ)) cblk (k + 2)
        = designSweep (fun s p => chartPert s p) Q u (fun j => blk j t₀) cblk (k + 2) := by
      unfold designSweep blockPlane
      simp only [map_add, blk_blkSpan_of_ne (k := k) (j := k + 2) (fin3_add_two_ne k), add_zero]
    rw [hchart, hsweep]
    exact hδ.choose_spec.2 x hx

end

end Work.Drive
