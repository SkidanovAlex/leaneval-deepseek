import Mathlib
import Submission.Work.Drive.perturbedTripleIdentity
import Submission.Work.Drive.ppDesignInputs
import Submission.Work.Drive.contMDiff_rotPresentation

/-!
# The block vocabulary of the design's perturbed triple: the structural bridges

`Work.Drive.blockChart`, `Work.Drive.blockPlane` and `Work.Drive.designSweep`
(`Submission/Work/Drive/perturbedTripleIdentity.lean`) present the `k`-th block of the design's
perturbed triple: the chart `Ξ (τ k) ∘ rotCapping (u k) ∘ Q`, the plane presentation
`Ξ (τ k) ∘ rotPresentation Q (u k)` and its radial sweep at the level `cblk k`.

This file contains the three *structural* facts that the transport `T6` consumes at each block, all
of them definitional or one-line corollaries:

* `Work.Drive.diskPlane_blockChart` — `blockPlane Ξ Q u τ k` **is** the disk presentation
  `diskPlane (blockChart Ξ Q u τ k)` (the perturbation is applied pointwise, so it passes through
  `diskPlane`);
* `Work.Drive.designSweep_eq_diskPlane` — hence the block's sweep is the clamped sweep of that disk
  presentation;
* `Work.Drive.blockChart_seam` — the block's chart inherits the chart's seam clause;
* `Work.Drive.contMDiff_apply_of_chartPert` (+ `contMDiff_blockPlane`, `contMDiff_designSweep`) — the
  smoothness of the block's plane presentation and sweep, from `ChartPert`'s joint smoothness clause.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The block's plane presentation is the disk presentation of the block's chart.**  The
perturbation `Ξ (τ k)` acts pointwise on `CappingSpace`, so it commutes with `diskPlane`. -/
theorem diskPlane_blockChart {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin m))
    (k : Fin 3) :
    diskPlane (blockChart Ξ Q u τ k) = blockPlane Ξ Q u τ k := by
  funext y
  rfl

/-- **The block's sweep is the clamped sweep of the block's disk presentation.** -/
theorem designSweep_eq_diskPlane {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin m))
    (cblk : Fin 3 → ℝ) (k : Fin 3) :
    designSweep Ξ Q u τ cblk k
      = clampedSweep (cblk k) (fun t => 1 - t) (diskPlane (blockChart Ξ Q u τ k)) := by
  rw [designSweep, diskPlane_blockChart]

/-- **The block's chart inherits the chart's seam clause.** -/
theorem blockChart_seam {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin m))
    (k : Fin 3) (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) :
    ∀ z : ℂ, ‖z‖ = 1 → blockChart Ξ Q u τ k (-z) = blockChart Ξ Q u τ k z := by
  intro z hz
  simp only [blockChart, Function.comp_apply, hQseam z hz]

/-- **The pointwise smoothness of a chart perturbation family** at a fixed parameter, from
`ChartPert`'s joint smoothness clause. -/
theorem contMDiff_apply_of_chartPert {Q : ℂ → CappingSpace} {m : ℕ}
    {Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace} (hΞ : ChartPert Q m Ξ)
    (s : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : CappingSpace => Ξ s p) :=
  hΞ.2.1.comp (contMDiff_const.prodMk contMDiff_id)

/-- **Smoothness of the block's plane presentation.** -/
theorem contMDiff_blockPlane {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (hΞsm : ∀ s : EuclideanSpace ℝ (Fin m),
      ContMDiff (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : CappingSpace => Ξ s p))
    (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin m))
    (k : Fin 3)
    (hQ : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (diskPlane Q)) :
    ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (blockPlane Ξ Q u τ k) :=
  (hΞsm (τ k)).comp (contMDiff_rotPresentation Q (u k) hQ)

/-- **Smoothness of the block's sweep.** -/
theorem contMDiff_designSweep {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (hΞsm : ∀ s : EuclideanSpace ℝ (Fin m),
      ContMDiff (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : CappingSpace => Ξ s p))
    (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle) (τ : Fin 3 → EuclideanSpace ℝ (Fin m))
    (cblk : Fin 3 → ℝ) (k : Fin 3)
    (hQ : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (diskPlane Q)) :
    ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (designSweep Ξ Q u τ cblk k) :=
  contMDiff_clampedSweep (cblk k) (fun t => 1 - t) (blockPlane Ξ Q u τ k)
    (by fun_prop) (contMDiff_blockPlane Ξ hΞsm Q u τ k hQ)

end

end Work.Drive
