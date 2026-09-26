import Mathlib
import Submission.Work.Smooth.OneManifold.Basic
import Submission.Work.Smooth.OneManifold.Plane.Basic

/-!
# Assembling local Euclidean structure from locally Euclidean open pieces

If every point of a subset `Z` of the surface has a neighbourhood `U`, open in the surface, for
which the trace `U ∩ Z` is locally Euclidean of dimension one, then so is `Z`: the pieces
`U ∩ Z` are open in `Z` and cover it.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.OneManifold

noncomputable section

/-- **Local Euclidean structure from a cover by locally Euclidean traces.** -/
theorem isLocallyEuclidean_of_forall_exists {ψ : Submission.Diffeo} {Z : Set R3}
    (hZ : Z ⊆ (Work.Smooth.Morse.torus ψ).carrier)
    (H : ∀ x : Z, ∃ U : Set R3, Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) U ∧
      (x : R3) ∈ U ∧ IsLocallyEuclidean (U ∩ Z)) :
    IsLocallyEuclidean Z := by
  classical
  choose U hUopen hxU hUloc using H
  refine isLocallyArc_of_isOpen_cover (ι := ↥Z) (X := ↥Z)
    (U := fun x => Subtype.val ⁻¹' (U x)) ?_ ?_ ?_
  · intro x
    exact isOpenInSet_of_isOpenInCarrier hZ (hUopen x)
  · intro x
    exact ⟨x, hxU x⟩
  · intro x
    have h1 : Work.Smooth.SphereJordan.IsLocallyArc
        ↥{y : ↥Z | (y : R3) ∈ U x ∩ Z} :=
      isLocallyArc_of_homeomorph (Work.Smooth.SphereJordan.LocalArc.subtypeSubtypeHomeomorph
        (show U x ∩ Z ⊆ Z from inter_subset_right)) (hUloc x)
    exact isLocallyArc_of_eq (by
      ext y
      exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩) h1

end

end Work.Smooth.OneManifold
