import Submission.Work.Topology.SphereSlicing.Defs
import Submission.Work.Topology.SphereSlicing.Slice.Reduce
import Submission.Work.Topology.SphereSlicing.cleansDiscs_of_cleanOneCurve

/-!
# Pardon's PL input repaired: spheres in general position

`Work.InnermostDisk.SphereSlicingInput P` and `Work.InnermostDisk.PardonPLInput P` quantify over
*all* embedded spheres, which is too much: a sphere whose intersection with `F` is two-dimensional
is not sliced by `F`, yet is an embedded sphere — see the configuration discussed for
`TransverseSphere` in `Work.Topology.SphereSlicing.Defs` (mathematical argument, not formalized
here).  Any theorem proved from `PardonPLInput` is vacuous where such a sphere is reachable; this
affects in particular the plan of closing `Work.BoxBubble.mustbeinessentialBox` through
`Work.InnermostDisk.mustbeinessential_of_PLInput`.

This file provides the repair: the same two inputs with the general-position hypothesis `S`
transverse to `F` added, the derivation from the chapter's `ClassicalInput`, and the verbatim
recovery of the conclusion of `Work.InnermostDisk.mustbeinessential_of_PLInput` from the repaired
hypothesis.  Everything a downstream user has to do is supply transversality of the one sphere they
care about — which is exactly Pardon's standing assumption ("`S` transverse to `F` and `β`") and in
the application is achieved by choosing the box in general position.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.SphereSlicing

noncomputable section

/-- **The slicing input, restricted to spheres in general position**: every embedded sphere
transverse to `F` is sliced by it.  This is `SphereSlicingInput` corrected by the transversality
hypothesis that Pardon's argument actually assumes. -/
def SphereSlicingInputOnGeneralPosition (P : ParamTorus) : Prop :=
  ∀ S : Set R3, IsEmbeddedSphere S → TransverseSphere P S → Nonempty (SphereSlicing P S)

/-- **Pardon's PL input, restricted to spheres in general position.** -/
def PardonPLInputOnGeneralPosition (P : ParamTorus) : Prop :=
  SphereSlicingInputOnGeneralPosition P ∧ CleansDiscs P

/-- The chapter's slicing input gives the general-position slicing input. -/
theorem sphereSlicingInputOnGeneralPosition_of_sliceInput {P : ParamTorus} (h : SliceInput P) :
    SphereSlicingInputOnGeneralPosition P :=
  fun S hS hT => nonempty_sphereSlicing_of_sliceInput h hS hT

/-- The chapter's classical input gives the general-position PL input. -/
theorem pardonPLInputOnGeneralPosition_of_classicalInput {P : ParamTorus}
    (h : ClassicalInput P) : PardonPLInputOnGeneralPosition P :=
  ⟨sphereSlicingInputOnGeneralPosition_of_sliceInput h.1, cleansDiscs_of_cleanOneCurve h.2⟩

/-- **Pardon's Lemma 4.2 from the repaired PL input**, with the same conclusion as
`Work.InnermostDisk.mustbeinessential_of_PLInput`.

Note that the existing theorem cannot be applied here: its hypothesis is the `Prop`
`Work.InnermostDisk.PardonPLInput P`, whose first conjunct quantifies over *all* embedded spheres
and is false, so no instance of it can be manufactured from a general-position hypothesis at one
sphere.  The repair therefore goes through `Work.InnermostDisk.mustbeinessential_of_inputs`, which
takes Pardon's first innermost input at the given sphere — here produced from the general-position
slicing input. -/
theorem mustbeinessential_of_pardonPLInputOnGeneralPosition (P : ParamTorus) (β : ClosedCurve P)
    (S : Set R3) (hS : IsEmbeddedSphere S) (hT : TransverseSphere P S)
    (h : PardonPLInputOnGeneralPosition P)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α :=
  mustbeinessential_of_inputs P β S
    ((h.1 S hS hT).some.innermostDiscInput_of_slicing) h.2 hSβ

end

end Work.Topology.SphereSlicing
