import Mathlib
import Submission.Work.Drive.foldFlatProducers
import Submission.Work.Drive.refTripleProducerDefs
import Submission.Work.Drive.perturbedTripleIdentity

/-!
# The `FoldFlat` instances of the design's own plane presentations

`Work.Drive.hasClassLinearization_of_endData` (§2.5) and `Work.Drive.exists_homotopy_meet3Hyp_encoded`
(§2.1) take the fold flatness of the design's plane class maps as hypotheses (`hLfold`, `hPfold`).  With
the two generic producers of `Drive/foldFlatProducers.lean` the design-shaped instances are one-liners;
this file spells them out so that the call sites of both lanes (the `hn2` producer and `hdense`) can use
them directly:

* `Work.Drive.foldFlat_refBlock` — the **`hn2` reference triple**
  `refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t k`: blocks `0`, `1` are the
  chart-perturbed rotations of `Q` (generic producer `foldFlat_chartPert_rotPresentation`), block `2` is
  the chart-perturbed *linear* reference plane (generic producer `foldFlat_chartPert_diskPlane`).
* `Work.Drive.foldFlat_blockPlane` — the **`hdense` design's** perturbed rotated blocks
  `blockPlane (fun s p => chartPert s p) Q u τ k`.
* `Work.Drive.foldFlat_family_linPlaneChart` (in `foldFlatProducers.lean`) — the `hLfold` shape, i.e. the
  linear disk models.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace
attribute [local instance] Work.Drive.projCharted
local instance instIsManifoldProjFoldFlatD :
    IsManifold (𝓡 3) Work.Drive.Ctop (Projectivization ℝ (Eucl 3)) :=
  Work.Drive.isManifold_projCharted 3

noncomputable section

/-- **The `hPfold` producer for the `hn2` reference triple.** -/
theorem foldFlat_refBlock (Q : ℂ → CappingSpace) (hQ : IsSmoothChart Q)
    (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (lam : ℝ) (hlam : 0 < lam)
    (u v : UnitAddCircle) (t : EuclideanSpace ℝ (Fin 12)) :
    ∀ k : Fin 3, FoldFlat (planeClassMap
      (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t k)) := by
  have h0 : refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0
      = fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk 0 t) (rotPresentation Q u y) := by
    funext y
    simp [refBlock, refTriple]
  have h1 : refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 1
      = fun y : EuclideanSpace ℝ (Fin 2) => chartPert (blk 1 t) (rotPresentation Q v y) := by
    funext y
    simp [refBlock, refTriple]
  have h2 : refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2
      = fun y : EuclideanSpace ℝ (Fin 2) =>
          chartPert (blk 2 t) (diskPlane (linPlaneChart (φ 2) lam hlam) y) := by
    funext y
    simp [refBlock, refTriple, refPlanePres]
  intro k
  fin_cases k
  · show FoldFlat (planeClassMap
      (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 0))
    rw [h0]
    exact foldFlat_chartPert_rotPresentation Q u (blk 0 t) hQ
  · show FoldFlat (planeClassMap
      (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 1))
    rw [h1]
    exact foldFlat_chartPert_rotPresentation Q v (blk 1 t) hQ
  · show FoldFlat (planeClassMap
      (refBlock (fun s p => chartPert s p) Q (refPlanePres φ lam hlam) u v t 2))
    rw [h2]
    exact foldFlat_chartPert_diskPlane (linPlaneChart (φ 2) lam hlam) (blk 2 t)
      (linPlaneChart_contMDiff (φ 2) lam hlam)

/-- **The `hPfold` producer for the design's perturbed rotated triple** (`blockPlane`). -/
theorem foldFlat_blockPlane (Q : ℂ → CappingSpace) (u : Fin 3 → UnitAddCircle)
    (τ : Fin 3 → Eucl 3) (hQ : IsSmoothChart Q) :
    ∀ k : Fin 3,
      FoldFlat (planeClassMap (blockPlane (fun s p => chartPert s p) Q u τ k)) :=
  fun k => foldFlat_chartPert_rotPresentation Q (u k) (τ k) hQ

end

end Work.Drive
