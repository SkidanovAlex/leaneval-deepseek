import Mathlib
import Submission.Work.Smooth.Plane.All

/-!
# Tameness of the slice from the planar slicing datum

`Work.Smooth.Plane.SlicedPlane P D` is `Nonempty (PlaneSlicing P D)`: the flat region `D` is cut
by the surface `F = P.carrier` into finitely many pairwise disjoint embedded circles and arcs of
`F`, each circle bounds an embedded disc inside `D`, the discs are nested and every loop of `F`
lying in `D` lies on one of the pieces (`PlaneSlicing.covers`).

`Work.Smooth.Plane.TransversePlane P D` is the general-position predicate: the same family covers
every *point* of `F ∩ D`, i.e. `F ∩ D` is the disjoint union of the circles and the arcs.

The only difference between the two is the covering field, and the loop covering implies the point
covering by a trivial specialisation: a point `x ∈ D ∩ F` is the image of the **constant**
`ClosedCurve P` at `x` (no non-degeneracy is required of `ClosedCurve P`), whose range is the
singleton `{x}`.

## Main result

* `Work.CountedPinch.tameSlice_of_slicedPlane` — `SlicedPlane P D → TransversePlane P D`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CountedPinch

theorem tameSlice_of_slicedPlane {P : Work.CoreTopology.ParamTorus} {D : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (h : Work.Smooth.Plane.SlicedPlane P D) : Work.Smooth.Plane.TransversePlane P D := by
  obtain ⟨S⟩ := h
  refine ⟨S.ι, S.fintype, S.c, S.κ, S.fintypeκ, S.a, S.simple, S.disjoint, S.mem, S.a_inj,
    S.a_mem, S.a_surface, S.a_disjoint, S.a_disjoint_c, ?_⟩
  -- the point covering: specialise the loop covering to the constant loop at `x`
  intro x hxD hxP
  let γ : Work.CoreTopology.ClosedCurve P :=
    ⟨fun _ => x, continuous_const, fun _ => rfl, fun _ => hxP⟩
  have hγ : ∀ t : ℝ, γ.γ t ∈ D := fun _ => hxD
  rcases S.covers γ hγ with ⟨i, hi⟩ | ⟨j, hj⟩
  · exact Or.inl ⟨i, hi ⟨0, rfl⟩⟩
  · exact Or.inr ⟨j, hj ⟨0, rfl⟩⟩

end Work.CountedPinch
