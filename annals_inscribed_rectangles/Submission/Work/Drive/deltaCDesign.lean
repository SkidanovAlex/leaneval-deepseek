import Mathlib
import Submission.Work.Drive.deltaCShift
import Submission.Work.Drive.blockVocabulary
import Submission.Work.Drive.perturbedTripleIdentity
import Submission.Work.Sard.interior_image_eq_empty_of_contMDiff_of_lt

/-!
# The `δc` conjunct of the design's transport `T6`, produced by moving one block

`Work.Drive.exists_deltaC_shift` (`Submission/Work/Drive/deltaCShift.lean`) produces the third conjunct
of `Work.Drive.T6GenAt` for a chart of the form `z ↦ Ξ (s₀ + σ) (Q' z)`, given that the chain's image
over the parameter box has empty interior.  This file instantiates it at the design's block `k`

* chart `blockChart chartPert Q u τ k = z ↦ chartPert (τ k) (rotCapping (u k) (Q z))`,
* sweep `clampedSweep c₂ (fun t => 1 - t) (blockPlane chartPert Q u τ (k+2))`,

with the empty-interior input supplied by the weak-Sard chapter of the workspace
(`Work.Sard.interior_image_eq_empty_of_contMDiff_of_lt`, applied to the sweep, a `C^∞` map
`𝔼³ → CappingSpace`).

For the design's joint genericity this is the missing step for the *third* conjunct of `T6GenAt`: the
other conjuncts are open in the parameter (`Work.Drive.eventually_goodLoopChain_design` and the two
Sard statements of `NOTES_LEAD_hdense.md` §5 P2), so after satisfying them one may move the block `k`
parameter by a small `σ` — the open ones persist — and this file supplies the cut avoidance there.
-/

namespace Work.Drive

open scoped Topology Manifold ContDiff
open Filter Set

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The `δc` conjunct of the design's block `k`, by a small move of the block `k` parameter.**
For any honest chart data `Q`, angles `u`, parameters `τ`, block `k`, level `c₂` and base parameter
`s₀`, and every `ε > 0`, there is `σ` of norm `< ε` such that the perturbed block-`k` chart satisfies
the cut avoidance against the sweep of the block `k+2` (whose parameters are held fixed). -/
theorem exists_deltaC_design {Q : ℂ → CappingSpace} (hQ : IsChartData Q)
    (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin 4)) (k : Fin 3)
    (c₂ : ℝ) (s₀ : EuclideanSpace ℝ (Fin 4)) (ε : ℝ) (hε : 0 < ε) :
    ∃ σ : EuclideanSpace ℝ (Fin 4), ‖σ‖ < ε ∧
      ∃ δc : ℝ, 0 < δc ∧ ∀ x : EuclideanSpace ℝ (Fin 2), ‖cplxOf x‖ ≤ δc →
        x ∉ diskCut (blockChart (fun s p => chartPert s p) Q u (Function.update τ k (s₀ + σ)) k)
          (clampedSweep c₂ (fun t => 1 - t)
            (blockPlane (fun s p => chartPert s p) Q u τ (k + 2))) := by
  have hΞ : ChartPert (fun z : ℂ => rotCapping (u k) (Q z)) 4 (fun s p => chartPert s p) :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  set W : EuclideanSpace ℝ (Fin 3) → CappingSpace :=
    clampedSweep c₂ (fun t => 1 - t) (blockPlane (fun s p => chartPert s p) Q u τ (k + 2)) with hWdef
  have hWsm : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) W := by
    rw [hWdef]
    exact contMDiff_clampedSweep c₂ (fun t => 1 - t)
      (blockPlane (fun s p => chartPert s p) Q u τ (k + 2)) (by fun_prop)
      (contMDiff_blockPlane (fun s p => chartPert s p)
        (fun s => contMDiff_apply_of_chartPert hΞ s) Q u τ (k + 2)
        (contMDiff_diskPlane (Q := Q) hQ.1))
  have hWint : interior (W '' Submission.Drive.unitBox 2) = ∅ :=
    Sard.interior_image_eq_empty_of_contMDiff_of_lt (m := 3) (n := 4) (by norm_num)
      W hWsm (Submission.Drive.unitBox 2)
  obtain ⟨σ, hσ, hδ⟩ := exists_deltaC_shift (Q' := fun z : ℂ => rotCapping (u k) (Q z))
    ((continuous_rotCapping (u k)).comp hQ.1.continuous) hΞ W hWsm.continuous hWint s₀ ε hε
  have hchart : (fun z : ℂ => chartPert (s₀ + σ) (rotCapping (u k) (Q z)))
      = blockChart (fun s p => chartPert s p) Q u (Function.update τ k (s₀ + σ)) k := by
    funext z
    simp only [blockChart, Function.update_self]
  refine ⟨σ, hσ, ?_⟩
  rw [hWdef] at hδ
  rw [← hchart]
  exact hδ

end

end Work.Drive
