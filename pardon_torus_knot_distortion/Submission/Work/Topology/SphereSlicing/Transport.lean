import Submission.Work.Topology.SphereSlicing.Defs
import Submission.Work.Topology.SphereSlicing.sliceData_map_homeomorph_iff
import Submission.Work.Topology.SphereSlicing.cleanOneCurve_map_homeomorph_iff
import Submission.Work.Topology.SphereSlicing.transverseSphere_map_homeomorph_iff

/-!
# The classical input is an invariant of the ambient homeomorphism class

The tori of Pardon's theorem are the images `F = ψ(F_standard)` of the standard torus of
revolution under a homeomorphism `ψ` of `ℝ³`.  The two halves of the classical input of this
chapter are invariants of that presentation:

* `sliceInput_map_homeomorph_iff` — slicing the spheres (in general position) by `F = ψ(F_standard)`
  is the same problem as slicing them by the standard torus;
* `cleanOneCurve_map_homeomorph_iff` — likewise for the single cut-and-paste;
* `classicalInput_map_homeomorph_iff` — hence the complete classical input
  `ClassicalInput (ParamTorus.mapHomeomorph ψ)` is *equivalent* to `ClassicalInput standard`.

The upshot for Pardon's argument: it suffices to prove the classical input for the *standard* torus
of revolution — a fixed, round geometric configuration — and the box computations of Pardon's
sweep live in the coordinates of the standard torus anyway.  The transport itself is
`ClosedCurve.mapHomeomorph`/`mapHomeomorphInv` for the curves, `φ ∘ ·` for the discs, and the
homeomorphism `↥S ≃ₜ ↥(φ '' S)` for the openness of the interior of a disc; see
`Work.Topology.SphereSlicing.SliceData.mapForward`/`mapBack` and
`Work.Topology.SphereSlicing.SliceDisc.push`/`pull`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.SphereSlicing

noncomputable section

/-- **The slicing input is invariant under an ambient homeomorphism.** -/
theorem sliceInput_map_homeomorph_iff (φ : R3 ≃ₜ R3) :
    SliceInput (ParamTorus.mapHomeomorph φ) ↔ SliceInput standard := by
  constructor
  · intro h S hS hT
    have hS' : IsEmbeddedSphere (φ '' S) := isEmbeddedSphere_image_homeomorph φ hS
    have hT' : TransverseSphere (ParamTorus.mapHomeomorph φ) (φ '' S) :=
      (transverseSphere_map_homeomorph_iff φ S).mpr hT
    exact (sliceData_map_homeomorph_iff φ S).mp ⟨(h (φ '' S) hS' hT').some⟩
  · intro h S hS hT
    have himg : φ '' (φ.symm '' S) = S := Equiv.image_symm_image φ.toEquiv S
    have hS' : IsEmbeddedSphere (φ.symm '' S) :=
      isEmbeddedSphere_image_homeomorph φ.symm hS
    have hT'' : TransverseSphere (ParamTorus.mapHomeomorph φ) (φ '' (φ.symm '' S)) := by
      rw [himg]; exact hT
    have hT' : TransverseSphere standard (φ.symm '' S) :=
      (transverseSphere_map_homeomorph_iff φ (φ.symm '' S)).mp hT''
    have h1 : Nonempty (SliceData standard (φ.symm '' S)) :=
      ⟨(h (φ.symm '' S) hS' hT').some⟩
    have h2 : Nonempty (SliceData (ParamTorus.mapHomeomorph φ) (φ '' (φ.symm '' S))) :=
      (sliceData_map_homeomorph_iff φ (φ.symm '' S)).mpr h1
    rwa [himg] at h2

/-- **The classical input of the chapter is invariant under an ambient homeomorphism**, so it
suffices to prove it for the standard torus of revolution. -/
theorem classicalInput_map_homeomorph_iff (φ : R3 ≃ₜ R3) :
    ClassicalInput (ParamTorus.mapHomeomorph φ) ↔ ClassicalInput standard := by
  unfold ClassicalInput
  rw [sliceInput_map_homeomorph_iff, cleanOneCurve_map_homeomorph_iff]

end

end Work.Topology.SphereSlicing
