import Submission.Work.Topology.Classical.Defs
import Submission.Work.Topology.Classical.exists_homeomorph_roundSphere
import Submission.Work.Topology.Classical.sliceData_standard_of_homeomorph

/-!
# `SliceInput standard` from Jordan–Schoenflies on the round sphere

The classical slicing input `Work.Topology.SphereSlicing.SliceInput standard` is *proved* here from
the single hypothesis `Work.Topology.Classical.JordanSchoenfliesSphere`, by transporting the round
sphere to the given embedded sphere:

* `Work.Topology.Classical.exists_homeomorph_roundSphere` supplies the homeomorphism
  `RoundSphere ≃ₜ S` from `IsEmbeddedSphere S` (a continuous injection out of a compact space into
  a Hausdorff space is an embedding);
* `Work.Topology.Classical.sliceData_standard_of_homeomorph` — the substance of the transport —
  pulls the transversality witness `TransverseSphere standard S` back to the round sphere, applies
  Jordan–Schoenflies there, and pushes the resulting nested discs forward along the
  homeomorphism.

Nothing else is used: in particular no Jordan curve theorem, no PL transversality and no
Alexandrov/Čech-type compactness argument enter. -/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.Classical

noncomputable section

/-- **The slicing input of the chapter for the standard torus of revolution, from
Jordan–Schoenflies on the round sphere.** -/
theorem sliceInput_standard_of_jordanSchoenflies (h : JordanSchoenfliesSphere) :
    Work.Topology.SphereSlicing.SliceInput standard := by
  intro S hS hT
  obtain ⟨φ, _⟩ := exists_homeomorph_roundSphere S hS
  exact sliceData_standard_of_homeomorph S φ hT h

/-- The same in the general-position vocabulary of `Work.Topology.SphereSlicing.GeneralPosition`:
`SliceInput standard` gives the (non-vacuous) PL input, so in particular Pardon's first
innermost-disc input is available at every embedded sphere in general position. -/
theorem sphereSlicingInputOnGeneralPosition_standard_of_jordanSchoenflies
    (h : JordanSchoenfliesSphere) :
    Work.Topology.SphereSlicing.SphereSlicingInputOnGeneralPosition standard :=
  Work.Topology.SphereSlicing.sphereSlicingInputOnGeneralPosition_of_sliceInput
    (sliceInput_standard_of_jordanSchoenflies h)

/-- **`SliceInput` at the tori of the challenge**, `P = mapHomeomorph ψ`: the classical slicing
input is an invariant of the ambient homeomorphism class
(`Work.Topology.SphereSlicing.sliceInput_map_homeomorph_iff`), so Jordan–Schoenflies on the round
sphere slices the spheres in general position by `ψ(F_standard)` as well. -/
theorem sliceInput_mapHomeomorph_of_jordanSchoenflies (ψ : R3 ≃ₜ R3)
    (h : JordanSchoenfliesSphere) :
    Work.Topology.SphereSlicing.SliceInput (ParamTorus.mapHomeomorph ψ) :=
  (Work.Topology.SphereSlicing.sliceInput_map_homeomorph_iff ψ).mpr
    (sliceInput_standard_of_jordanSchoenflies h)

/-- **The slicing of the box boundary** `∂PBox s c σ = BoxSphere s c σ` by the standard torus, from
Jordan–Schoenflies on the round sphere: the case of the classical input which Pardon's sweep
actually uses when `P = standard`.  (For `P = mapHomeomorph ψ` the transfer is
`Work.Topology.SphereSlicing.sliceData_map_homeomorph_iff`, or
`sliceInput_mapHomeomorph_of_jordanSchoenflies`.) -/
theorem sliceData_BoxSphere_of_jordanSchoenflies (h : JordanSchoenfliesSphere) {s : ℝ}
    (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hT : Work.Topology.SphereSlicing.TransverseSphere standard
      (Work.Topology.SphereSlicing.BoxSphere s c σ)) :
    Nonempty (Work.Topology.SphereSlicing.SliceData standard
      (Work.Topology.SphereSlicing.BoxSphere s c σ)) :=
  sliceInput_standard_of_jordanSchoenflies h _
    (Work.Topology.SphereSlicing.isEmbeddedSphere_BoxSphere hs c σ) hT

end

end Work.Topology.Classical
