import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs

/-!
# The slice of the sphere is exactly the union of the slicing curves

Let `P` be a parametrised torus with surface `F = P.carrier` and let `S` be a set of `ℝ³` equipped
with a slicing datum `Work.Topology.SphereSlicing.SliceData P S`.

Two of its fields pin down `S ∩ F` from either side:

* `SliceData.mem` says every curve `c i` lies in `S`, and `ClosedCurve.mem` says it lies in `F`,
  so each `Set.range (c i).γ` is contained in `S ∩ F`;
* `SliceData.covers_pt` says conversely that every point of `S ∩ F` lies on one of the curves.

Hence
`S ∩ P.carrier = ⋃ i : h.ι, Set.range (h.c i).γ`,

which is the "curve part" of the slicing datum in closed form: the intersection of the sphere with
the surface *is* the union of the curves, with no extra points.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology

namespace Work.Topology.SphereSlicing

noncomputable section

theorem sliceData_inter_eq_iUnion {P : Work.CoreTopology.ParamTorus}
    {S : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (h : Work.Topology.SphereSlicing.SliceData P S) :
    S ∩ P.carrier = ⋃ i : h.ι, Set.range (h.c i).γ := by
  ext x
  constructor
  · -- a point of `S ∩ F` lies on one of the curves
    rintro ⟨hxS, hxF⟩
    obtain ⟨i, hi⟩ := h.covers_pt x hxS hxF
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  · -- a point of a curve lies in `S` (field `mem`) and in `F` (`ClosedCurve.mem`)
    intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨t, rfl⟩ := hi
    exact ⟨h.mem i t, (h.c i).range_subset_carrier ⟨t, rfl⟩⟩

end

end Work.Topology.SphereSlicing
