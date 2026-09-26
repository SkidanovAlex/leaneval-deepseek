import Submission.Work.PlaneSlice.Obstruction
import Submission.Work.BoxShrink.Core.Defs
import Submission.Work.BoxShrink.cruxAE
import Submission.Work.Smooth.Plane.Cleaning

/-!
# The slice of Pardon's box is cleaned almost everywhere

This file delivers item (3) of the `Submission/Work/PlaneSlice` assignment: Pardon's planar
innermost step **almost everywhere** for the slices of Pardon's box,

`∀ᵐ u, Work.InnermostDisk.CleansInSphere (torus ψ) (Work.BoxShrink.Core.cutDisc s c σ u)`,

from

* the almost-everywhere general position of the cutting plane (item (1),
  `Work.PlaneSlice.ae_isCircleUnion_pardonSlice`, which is `Work.PlaneSlice.ae_transversePlane_coord`
  composed with the classification of the level set — the corrected, non-vacuous route, with no
  `CompactOneManifoldInput`);
* the construction of the rings of the slice (item (2) in the corrected form,
  `Work.PlaneSlice.nonempty_sliceRings_of_isCircleUnion`);
* Pardon's first innermost step from the rings (`Work.PlaneSlice.innermostDiscInput_of_sliceRings`);
* the global cut-and-paste `Work.InnermostDisk.CleansDiscs`, which the rest of the workspace derives
  from the classical cut-and-paste (`Work.BoxShrink.cleansDiscsAll_of_pushThrough`).

The statement is *not* the `planarInnermost` field of `Work.BoxShrink.ClassicalInputs` (which asks
for **every** plane level `u`, and is therefore not available: degenerate levels are excluded by the
Sard step); it is the almost-everywhere form, which is what the sweep consumes by choosing the
plane level in general position.

## Main results

* `Work.PlaneSlice.AeCleansPardonSlice` — the almost-everywhere statement, as a named `Prop`;
* `Work.PlaneSlice.aeCleansPardonSlice` — it holds for every `ψ` with the global cut-and-paste at
  `torus ψ`;
* `Work.PlaneSlice.aeCleansPardonSlice_all`, `..._of_pushThrough` — the same for all `ψ` at once,
  from `Work.BoxShrink.CleansDiscsAll` or from the classical cut-and-paste
  `Work.Topology.Classical.PushThroughInnermost standard`;
* `Work.PlaneSlice.ae_cleansInSphere_pardonSlice_of_pushThrough` — the literal shape requested by
  the consumer.
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory
open scoped Topology ENNReal

namespace Work.PlaneSlice

noncomputable section

variable {ψ : Submission.Diffeo}

/-- **The almost-everywhere planar innermost statement at the slices of Pardon's box.**

For almost every plane level `u`, the slice `cutDisc s c σ u = PBox s c σ ∩ {y (σ 2) = c (σ 2) + u}`
can be cleaned: every essential loop of the surface inside it can be replaced by a simple essential
loop inside it bounding a disc whose interior is disjoint from the surface.

This is the named form of the statement which replaces the `planarInnermost` field of
`Work.BoxShrink.ClassicalInputs` in the ledger. -/
def AeCleansPardonSlice (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) : Prop :=
  ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
    Work.InnermostDisk.CleansInSphere (Work.Smooth.Morse.torus ψ)
      (Work.BoxShrink.Core.cutDisc s c σ u)

/-- **Item (3): the slices of Pardon's box are cleaned almost everywhere.**

The four ingredients are the almost-everywhere general position of the cutting plane (item (1)),
the rings of the slice (item (2)), Pardon's first innermost step, and the cut-and-paste. -/
theorem aeCleansPardonSlice (ψ : Submission.Diffeo)
    (hcl : Work.InnermostDisk.CleansDiscs (Work.Smooth.Morse.torus ψ)) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) : AeCleansPardonSlice ψ s c σ := by
  filter_upwards [ae_isCircleUnion_pardonSlice ψ c σ] with u hu
  have hconv : Convex ℝ (Work.BoxShrink.Core.cutDisc s c σ u) := by
    change Convex ℝ (Submission.PBox s c σ ∩ {y : R3 | y (σ 2) = c (σ 2) + u})
    exact Work.Smooth.Plane.convex_PardonSlice s c σ u
  have hplane : ∀ y ∈ Work.BoxShrink.Core.cutDisc s c σ u, y (σ 2) = c (σ 2) + u :=
    fun y hy => (Work.BoxShrink.Core.mem_cutDisc.mp hy).2
  obtain ⟨h⟩ := nonempty_sliceRings_of_isCircleUnion hconv hplane hu
  exact Work.InnermostDisk.cleansInSphere_of_inputs
    (innermostDiscInput_of_sliceRings h) hcl

/-- The same, with the cut-and-paste hypothesis at every torus of the challenge. -/
theorem aeCleansPardonSlice_all (hcl : Work.BoxShrink.CleansDiscsAll) :
    ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)),
      AeCleansPardonSlice ψ s c σ :=
  fun ψ s c σ => aeCleansPardonSlice ψ (hcl ψ) s c σ

/-- **The same, from the classical cut-and-paste at the standard torus**
(`Work.Topology.Classical.PushThroughInnermost standard`): Alexander's theorem for an embedded
`2`-sphere in `ℝ³` together with isotopy extension.  This is the exact form of the hypothesis under
which the ledger `Work.BoxShrink.ClassicalInputs` obtains its `cleans` field. -/
theorem aeCleansPardonSlice_of_pushThrough
    (h : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)),
      AeCleansPardonSlice ψ s c σ :=
  aeCleansPardonSlice_all (Work.BoxShrink.cleansDiscsAll_of_pushThrough h)

/-- **The literal shape of the statement for the consumer**: for every diffeomorphism `ψ` and every
height `s`, centre `c` and permutation `σ`, almost every plane level `u` cleans the slice
`cutDisc s c σ u` of the torus `mapHomeomorph ψ.toHomeomorph = torus ψ`, from the classical
cut-and-paste. -/
theorem ae_cleansInSphere_pardonSlice_of_pushThrough
    (h : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)),
      ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        Work.InnermostDisk.CleansInSphere
          (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
          (Work.BoxShrink.Core.cutDisc s c σ u) :=
  aeCleansPardonSlice_of_pushThrough h

/-- **The rings of the slice of Pardon's box, almost everywhere.**  The corrected slicing input for
the tori of the challenge: for almost every plane level `u` the slice `cutDisc s c σ u` carries the
ring datum `Work.PlaneSlice.SliceRings` from which Pardon's first innermost argument proceeds. -/
theorem ae_sliceRings_pardonSlice (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      Nonempty (SliceRings ψ (Work.BoxShrink.Core.cutDisc s c σ u)) := by
  filter_upwards [ae_isCircleUnion_pardonSlice ψ c σ] with u hu
  have hconv : Convex ℝ (Work.BoxShrink.Core.cutDisc s c σ u) := by
    change Convex ℝ (Submission.PBox s c σ ∩ {y : R3 | y (σ 2) = c (σ 2) + u})
    exact Work.Smooth.Plane.convex_PardonSlice s c σ u
  have hplane : ∀ y ∈ Work.BoxShrink.Core.cutDisc s c σ u, y (σ 2) = c (σ 2) + u :=
    fun y hy => (Work.BoxShrink.Core.mem_cutDisc.mp hy).2
  exact nonempty_sliceRings_of_isCircleUnion hconv hplane hu

/-- **The strengthened form: for almost every plane level `u`, *every* box height `s` is cleaned.**

The rings of the slice are built from the classification of the level set
`F ∩ {y (σ 2) = c (σ 2) + u}` alone — the height `s` of the box only selects which circles lie inside
the slice — so the exceptional set of plane levels can be taken independently of `s`.  This is the
form in which the sweep can choose the height freely once the plane level is fixed. -/
theorem ae_forall_cleansPardonSlice (ψ : Submission.Diffeo)
    (hcl : Work.InnermostDisk.CleansDiscs (Work.Smooth.Morse.torus ψ)) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∀ s : ℝ, Work.InnermostDisk.CleansInSphere (Work.Smooth.Morse.torus ψ)
        (Work.BoxShrink.Core.cutDisc s c σ u) := by
  filter_upwards [ae_isCircleUnion_pardonSlice ψ c σ] with u hu s
  have hconv : Convex ℝ (Work.BoxShrink.Core.cutDisc s c σ u) := by
    change Convex ℝ (Submission.PBox s c σ ∩ {y : R3 | y (σ 2) = c (σ 2) + u})
    exact Work.Smooth.Plane.convex_PardonSlice s c σ u
  have hplane : ∀ y ∈ Work.BoxShrink.Core.cutDisc s c σ u, y (σ 2) = c (σ 2) + u :=
    fun y hy => (Work.BoxShrink.Core.mem_cutDisc.mp hy).2
  obtain ⟨h⟩ := nonempty_sliceRings_of_isCircleUnion hconv hplane hu
  exact Work.InnermostDisk.cleansInSphere_of_inputs
    (innermostDiscInput_of_sliceRings h) hcl

/-- **The strengthened form for every torus of the challenge**: for almost every plane level `u`,
every box height `s` is cleaned, with the classical cut-and-paste as the only input. -/
theorem ae_forall_cleansPardonSlice_of_pushThrough
    (h : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)),
      ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        ∀ s : ℝ, Work.InnermostDisk.CleansInSphere (Work.Smooth.Morse.torus ψ)
          (Work.BoxShrink.Core.cutDisc s c σ u) :=
  fun ψ c σ => ae_forall_cleansPardonSlice ψ
    ((Work.BoxShrink.cleansDiscsAll_of_pushThrough h) ψ) c σ

/-- **For almost every plane level, every box height carries the ring datum** (the strengthened form
of `ae_sliceRings_pardonSlice`). -/
theorem ae_forall_sliceRings_pardonSlice (ψ : Submission.Diffeo) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      ∀ s : ℝ, Nonempty (SliceRings ψ (Work.BoxShrink.Core.cutDisc s c σ u)) := by
  filter_upwards [ae_isCircleUnion_pardonSlice ψ c σ] with u hu s
  have hconv : Convex ℝ (Work.BoxShrink.Core.cutDisc s c σ u) := by
    change Convex ℝ (Submission.PBox s c σ ∩ {y : R3 | y (σ 2) = c (σ 2) + u})
    exact Work.Smooth.Plane.convex_PardonSlice s c σ u
  have hplane : ∀ y ∈ Work.BoxShrink.Core.cutDisc s c σ u, y (σ 2) = c (σ 2) + u :=
    fun y hy => (Work.BoxShrink.Core.mem_cutDisc.mp hy).2
  exact nonempty_sliceRings_of_isCircleUnion hconv hplane hu

/-! ## The ledger form: `Work.BoxShrink.AePlaneCleaned`, and the capstone -/

/-- **`Work.BoxShrink.AePlaneCleaned` from the classical cut-and-paste.**

This is the exact `Prop` which `Submission/Work/BoxShrink/cruxAE.lean` carries in place of the
`planarInnermost` field of the ledger: the almost-everywhere cleaning of the flat disc
`cutDisc s c σ u` of Pardon's double bubble.  Hence Pardon's planar innermost step is no longer an
input of the reduction. -/
theorem aePlaneCleaned_of_pushThrough
    (h : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    Work.BoxShrink.AePlaneCleaned :=
  fun ψ c σ s => aeCleansPardonSlice_of_pushThrough h ψ s c σ

/-- **`Work.BoxShrink.AePlaneCleaned` from the cut-and-paste at every torus of the challenge.** -/
theorem aePlaneCleaned_of_cleansDiscsAll (hcl : Work.BoxShrink.CleansDiscsAll) :
    Work.BoxShrink.AePlaneCleaned :=
  fun ψ c σ s => aeCleansPardonSlice_all hcl ψ s c σ

/-- **The ledger shape, unfolded.**  `Work.BoxShrink.AePlaneCleaned` is *by definition* the
statement below; it is recorded here in unfolded form so that the consumer can use it without
depending on the exact location of the `def` in the sibling chapters. -/
theorem aePlaneCleaned_unfolded_of_pushThrough
    (h : Work.Topology.Classical.PushThroughInnermost Work.CoreTopology.standard) :
    ∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ),
      ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        Work.InnermostDisk.CleansInSphere
          (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
          (Work.BoxShrink.Core.cutDisc s c σ u) :=
  fun ψ c σ s => (ae_forall_cleansPardonSlice_of_pushThrough h ψ c σ).mono
    (fun u hu => hu s)

/-- The same, unfolded, from the cut-and-paste at every torus of the challenge. -/
theorem aePlaneCleaned_unfolded_of_cleansDiscsAll (hcl : Work.BoxShrink.CleansDiscsAll) :
    ∀ (ψ : Submission.Diffeo) (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ),
      ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        Work.InnermostDisk.CleansInSphere
          (Work.CoreTopology.ParamTorus.mapHomeomorph ψ.toHomeomorph)
          (Work.BoxShrink.Core.cutDisc s c σ u) :=
  fun ψ c σ s => (ae_forall_cleansPardonSlice ψ (hcl ψ) c σ).mono
    (fun u hu => hu s)

end

end Work.PlaneSlice
