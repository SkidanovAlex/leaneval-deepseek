import Mathlib
import Submission.Work.Drive.sideValue
import Submission.Work.Drive.rotCappingSmooth
import Submission.Work.Drive.contMDiff_rotCapping_family

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

attribute [local instance] Work.Drive.cappingCharted

/-- Smoothness of the rotated presentation of a plane from smoothness of the base presentation: the
rotation `Work.Drive.rotCapping w` acts on the plane by `Work.Drive.rotPresentation Q w y =
Work.Drive.rotCapping w (Work.Drive.diskPlane Q y)` (definitionally, as the reviewers verified), and the
fixed rotation is `C^∞` (`Work.Drive.contMDiffAt_rotCapping` of `rotCappingSmooth.lean`, pointwise in
`(t, p)`; the general angle `w : UnitAddCircle` is a coset of `ℝ` and hence of the form
`(t : UnitAddCircle)`, `QuotientAddGroup.mk_surjective`).

This is the `smooth` clause of `Work.Drive.Meet3Hyp` for the three swept chains
`clampedSweep (c k) ψ (rotPresentation Q (u k))` of the counting route. -/
theorem contMDiff_rotPresentation (Q : ℂ → Work.Drive.CappingSpace) (w : UnitAddCircle)
    (hQ : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.diskPlane Q)) :
    ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (Work.Drive.rotPresentation Q w) := by
  -- write the rotation angle as the class of a real number
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective w
  rw [← ht]
  -- the rotated presentation is the fixed rotation applied to the base presentation
  have hfun : (Work.Drive.rotPresentation Q ((t : ℝ) : UnitAddCircle))
      = fun y => rotCapping ((t : ℝ) : UnitAddCircle) (Work.Drive.diskPlane Q y) := by
    funext y
    rw [Work.Drive.rotPresentation, Work.Drive.diskPlane_apply, Work.Drive.diskPlane_apply]
  rw [hfun]
  -- a fixed rotation of the capping space preserves smoothness (`contMDiffAt_rotCapping_family`)
  intro y
  exact contMDiffAt_rotCapping_family (fun _ : EuclideanSpace ℝ (Fin 2) => t)
    (Work.Drive.diskPlane Q) contMDiff_const hQ y

end Work.Drive
