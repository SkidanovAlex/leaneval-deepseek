import Submission.Work.Drive.EpsFormSphere.Defs
import Submission.Work.Drive.EpsFormSphere.Convert
import Submission.Work.BoxShrink.Core.Defs

/-!
# Compatibility re-export for the ε-form of Pardon's Lemma 3

This module is a **name-compatibility re-export**, created by the agent owning
`Submission/Work/Drive/Final/slice_avoiding_loop.lean` to restore the build.

`Submission/Work/EpsW/Defs.lean` (line 3) imports
`Submission.Work.Drive.EpsFormSphere.countingHalfEpsSphere`, but no file of that name existed in the
tree: the statement it used to contain, `Work.Drive.EpsSphere.CountingHalfEpsSphere`, together with
its companion `ThickHalf`, lives in `Submission/Work/Drive/EpsFormSphere/Defs.lean` (already imported
by the line above in `EpsW/Defs.lean`).  The import is therefore a *stale reference to a renamed
module*; importing this file restores the resolution of `EpsW/Defs.lean` (and of every module
importing it).

The one declaration that the consumers of the phantom module need and that is not in the tree is
`Work.Drive.EpsFormSphere.thickHalf_of_closedHalf` (used by `Work.Drive.EpsFormSphere.cruxEpsFormW_of_closedHalf`
in `EpsW/Defs.lean`); it is proved below.  It is the point-set fact that the ε-form's conclusion is
*weaker* than the "closed half" form of the crux: a point in the closure of a half-region is within
any positive distance of the region, so an essential loop in the closure of the upper (resp. lower)
half-region witnesses `ThickHalf` at every `ε > 0`.

Do not add further mathematics here: the definitions and theorems of the ε-form are in
`…EpsFormSphere/Defs.lean` (`CountingHalfEpsSphere`, `ThickHalf`, `PinchEps`,
`countingHalfEpsSphere_of_pinchEps`, …) and `…EpsFormSphere/Convert.lean`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Metric

namespace Work.Drive.EpsFormSphere

noncomputable section

/-- **A loop in the closure of a half-region is within every `ε > 0` of that half-region.**  This is
the point-set content of the reduction of Pardon's ε-form to the "closed half" form of the crux
(`Work.Drive.EpsFormSphere.ClosedHalfCrux`): every point of `closure X` lies in `thickening ε X` as
soon as `ε > 0`. -/
theorem thickHalf_of_closedHalf {P : Work.CoreTopology.ParamTorus} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)}
    (h : (∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
          ∀ t : ℝ, γ t ∈ closure (Work.BoxShrink.Core.upperRegion P s c σ u)) ∨
        (∃ γ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P γ ∧
          ∀ t : ℝ, γ t ∈ closure (Work.BoxShrink.Core.lowerRegion P s c σ u)))
    (ε : ℝ) (hε : 0 < ε) :
    Work.Drive.EpsSphere.ThickHalf P s c σ u ε := by
  rcases h with ⟨γ, hγ, hmem⟩ | ⟨γ, hγ, hmem⟩
  · exact Or.inl ⟨γ, hγ, fun t => Metric.closure_subset_thickening hε _ (hmem t)⟩
  · exact Or.inr ⟨γ, hγ, fun t => Metric.closure_subset_thickening hε _ (hmem t)⟩

end

end Work.Drive.EpsFormSphere
