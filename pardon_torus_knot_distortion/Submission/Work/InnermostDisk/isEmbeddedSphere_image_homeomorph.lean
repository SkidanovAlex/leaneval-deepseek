import Mathlib
import Submission.Work.InnermostDisk.Defs

/-!
# Embedded spheres are preserved by homeomorphisms of `ℝ³`

`Work.InnermostDisk.IsEmbeddedSphere S` says that `S` is the image of the unit sphere
under an injective continuous map.  A homeomorphism `φ` of `ℝ³` carries such a sphere to
a sphere: the composite `φ ∘ e` is continuous and injective, and its range is `φ '' S`.
-/

namespace Work.InnermostDisk

theorem isEmbeddedSphere_image_homeomorph (φ : LeanEval.KnotTheory.PardonDistortion.R3 ≃ₜ LeanEval.KnotTheory.PardonDistortion.R3)
    {S : Set LeanEval.KnotTheory.PardonDistortion.R3} (h : Work.InnermostDisk.IsEmbeddedSphere S) :
    Work.InnermostDisk.IsEmbeddedSphere (φ '' S) := by
  obtain ⟨e, hinj, hrange⟩ := h
  refine ⟨⟨φ ∘ e, φ.continuous.comp e.continuous⟩, φ.injective.comp hinj, ?_⟩
  show Set.range (φ ∘ ⇑e) = φ '' S
  rw [Set.range_comp, hrange]

end Work.InnermostDisk
