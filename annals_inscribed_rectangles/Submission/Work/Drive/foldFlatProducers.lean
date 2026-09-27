import Mathlib
import Submission.Work.Drive.encodedEndData
import Submission.Work.Drive.mfderiv_planeClassMap_diskPlane_single
import Submission.Work.Drive.mfderiv_planeClassMap_chartPert_diskPlane_single
import Submission.Work.Drive.linearPlaneChart
import Submission.Work.Drive.contMDiff_rotPresentation
import Submission.Work.Drive.goodPair_rotCapping

/-!
# The `FoldFlat` producers of the ends clause

`Work.Drive.FoldFlat A` (`Drive/encodedEndData.lean`, the lead's `NOTES_LEAD_hodd_faces.md` §2) says
that the class map `A` of a plane presentation kills the *fold directions* `eᵢ` at every parameter with
`y i ∈ {0,1}`.  It is a **hypothesis** of `Work.Drive.exists_homotopy_meet3Hyp_encoded` (§2.1) and of
`Work.Drive.hasClassLinearization_of_endData` (§2.5: `hPfold` for the perturbed design planes and
`hLfold` for the linear disk models), and the two analytic bricks that make it a **theorem** for the
design's own presentations are on disk:

* `Work.Drive.mfderiv_planeClassMap_diskPlane_single` — the folded disk presentation `diskPlane Q` kills
  the fold directions (`Q` smooth);
* `Work.Drive.mfderiv_planeClassMap_chartPert_diskPlane_single` — and so does its chart perturbation
  `chartPert τ ∘ diskPlane Q`.

This file packages them as `FoldFlat` instances for the three presentation shapes the design uses:
the linear disk models `linPlaneChart φ c hc`, the perturbed presentations `chartPert τ ∘ diskPlane Q`,
and the perturbed *rotated* presentations `chartPert τ ∘ rotPresentation Q w` (the design's block
chains), together with the unperturbed rotated ones.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace
attribute [local instance] Work.Drive.projCharted
local instance instIsManifoldProjFoldFlat :
    IsManifold (𝓡 3) Work.Drive.Ctop (Projectivization ℝ (Eucl 3)) :=
  Work.Drive.isManifold_projCharted 3

noncomputable section

/-- **The fold flatness of a linear disk model.** -/
theorem foldFlat_diskPlane_linPlaneChart (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) :
    FoldFlat (planeClassMap (diskPlane (linPlaneChart φ c hc))) := by
  intro y i hy
  exact mfderiv_planeClassMap_diskPlane_single (linPlaneChart φ c hc) y i hy
    (linPlaneChart_contMDiff φ c hc)

/-- **The fold flatness survives the chart perturbation** (`Ξ (blk k t) ∘ P` for a `diskPlane`
presentation `P`). -/
theorem foldFlat_chartPert_diskPlane (Q : ℂ → CappingSpace) (τ : Eucl 3)
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q) :
    FoldFlat (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) => chartPert τ (diskPlane Q y))) := by
  intro y i hy
  exact mfderiv_planeClassMap_chartPert_diskPlane_single Q τ y i hy hQ

/-- **The fold flatness of a rotated presentation** (`rotPresentation Q w = diskPlane (rotCapping w ∘ Q)`
definitionally). -/
theorem foldFlat_rotPresentation (Q : ℂ → CappingSpace) (w : UnitAddCircle) (hQ : IsSmoothChart Q) :
    FoldFlat (planeClassMap (rotPresentation Q w)) := by
  have hrot : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop (fun z : ℂ => rotCapping w (Q z)) :=
    (contMDiff_rotCapping_apply w).comp hQ
  intro y i hy
  exact mfderiv_planeClassMap_diskPlane_single (fun z : ℂ => rotCapping w (Q z)) y i hy hrot

/-- **The fold flatness of a perturbed rotated presentation** — the shape of the design's block chains
`work.Drive.refBlock (fun s p => chartPert s p) Q R u v t k`. -/
theorem foldFlat_chartPert_rotPresentation (Q : ℂ → CappingSpace) (w : UnitAddCircle) (τ : Eucl 3)
    (hQ : IsSmoothChart Q) :
    FoldFlat (planeClassMap (fun y : EuclideanSpace ℝ (Fin 2) =>
      chartPert τ (rotPresentation Q w y))) := by
  have hrot : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop (fun z : ℂ => rotCapping w (Q z)) :=
    (contMDiff_rotCapping_apply w).comp hQ
  exact foldFlat_chartPert_diskPlane (fun z : ℂ => rotCapping w (Q z)) τ hrot

/-- The `hLfold`-shaped family: every chart of the linear family is fold flat. -/
theorem foldFlat_family_linPlaneChart (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) :
    ∀ k : Fin 3, FoldFlat (planeClassMap (diskPlane (linPlaneChart (φ k) c hc))) :=
  fun k => foldFlat_diskPlane_linPlaneChart (φ k) c hc

end

end Work.Drive
