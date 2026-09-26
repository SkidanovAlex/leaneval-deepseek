import Submission.Work.Topology.SphereSlicing.Defs

/-!
# The degenerate slicing: a sphere disjoint from the surface

The slicing datum `SliceData P S` is empty of content when `S` misses `F = P.carrier`: there are
no components of `S ∩ F` and every field is vacuous.  This file records that instance, so that
the reduction `SphereSlicing` ⟸ `SliceData` of `Work.Topology.SphereSlicing.Slice.Reduce` is seen
to be non-vacuous *unconditionally* in that case: a sphere disjoint from `F` is sliced by `F`.

This is the (trivial) base case of the classical slicing theorem; the substantive content of
`SliceInput` is the case in which `S` meets `F`, which is exactly where transversality and
Jordan–Schoenflies are needed.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.SphereSlicing

noncomputable section

/-- **The degenerate slicing.**  If `S` is disjoint from the surface `F = P.carrier`, then `S` is
sliced by `F` with no curves at all: `SliceData P S` holds with `ι = Empty`. -/
def sliceDataOfDisjoint {P : ParamTorus} {S : Set R3}
    (h : ∀ x : R3, x ∈ S → x ∉ P.carrier) : SliceData P S where
  ι := Empty
  fintype := inferInstance
  c := fun i => isEmptyElim i
  simple := fun i => isEmptyElim i
  disjoint := fun i => isEmptyElim i
  mem := fun i => isEmptyElim i
  covers_pt := fun x hxS hxc => (h x hxS hxc).elim
  disc := fun i => isEmptyElim i
  disc_inj := fun i => isEmptyElim i
  disc_boundary := fun i => isEmptyElim i
  disc_mem := fun i => isEmptyElim i
  open_interior := fun i => isEmptyElim i
  rank := fun i => isEmptyElim i
  inside := fun i => isEmptyElim i

/-- **A sphere disjoint from the surface is sliced by it** — unconditionally.  This is the
non-vacuity check for `Work.InnermostDisk.SphereSlicing`, and it is the base case of the descent
in Pardon's proof (a box far away from the surface contains no essential loop either). -/
theorem nonempty_sphereSlicing_of_disjoint {P : ParamTorus} {S : Set R3}
    (h : ∀ x : R3, x ∈ S → x ∉ P.carrier) : Nonempty (SphereSlicing P S) :=
  ⟨{ ι := Empty
     fintype := inferInstance
     c := fun i => isEmptyElim i
     simple := fun i => isEmptyElim i
     disjoint := fun i => isEmptyElim i
     mem := fun i => isEmptyElim i
     covers := fun γ hγ => (h (γ.γ 0) (hγ 0) (γ.mem 0)).elim
     disc := fun i => isEmptyElim i
     disc_inj := fun i => isEmptyElim i
     disc_boundary := fun i => isEmptyElim i
     disc_mem := fun i => isEmptyElim i
     rank := fun i => isEmptyElim i
     inside := fun i => isEmptyElim i
     inside_subset := fun i => isEmptyElim i
     covers_interior := fun i => isEmptyElim i }⟩

/-- **Transversality holds vacuously for a sphere disjoint from `F`**: the transversal family of
curves is empty.  This also shows that `TransverseSphere` (the general-position hypothesis under
which the slicing input is stated, see `Work.Topology.SphereSlicing.Defs`) is not a vacuous
predicate. -/
theorem transverseSphere_of_disjoint {P : ParamTorus} {S : Set R3}
    (h : ∀ x : R3, x ∈ S → x ∉ P.carrier) : TransverseSphere P S :=
  ⟨Empty, inferInstance, fun i => isEmptyElim i,
    ⟨fun i => isEmptyElim i, ⟨fun i => isEmptyElim i, ⟨fun i => isEmptyElim i,
      fun x hxS hxc => (h x hxS hxc).elim⟩⟩⟩⟩

/-- **A sphere disjoint from the surface contains no essential loop of it** — unconditionally, with
no classical input at all.  This is the base case of the descent in Pardon's argument (a region
avoiding the surface certainly contains no essential loop), and it shows that the conclusions of
this chapter are not vacuous in the degenerate case. -/
theorem not_containsEssentialLoop_of_disjoint {P : ParamTorus} {S : Set R3}
    (h : ∀ x : R3, x ∈ S → x ∉ P.carrier) : ¬ P.ContainsEssentialLoop S :=
  fun ⟨γ, _, hmem⟩ => h (γ.γ 0) (hmem 0) (γ.mem 0)

end

end Work.Topology.SphereSlicing
