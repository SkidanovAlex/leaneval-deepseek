import Mathlib
import Submission.Work.Smooth.Plane.Slicing
import Submission.Work.InnermostDisk.All

namespace Work.Smooth.Plane.Slicing

/-- The image of an arc of `F ∩ D` is compact (it is the image of the compact interval
`Work.Smooth.Plane.ArcInterval`), hence a closed subset of `ℝ³`. -/
theorem isClosed_range_arc (a : C(ArcInterval, LeanEval.KnotTheory.PardonDistortion.R3)) :
    IsClosed (Set.range a) := by
  have : CompactSpace ArcInterval :=
    isCompact_iff_compactSpace.mp (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  exact (isCompact_range a.continuous).isClosed

/-- **The components of a planar slice cover every loop contained in the slice.**

Let `h : Work.Smooth.Plane.PlaneSliceData P D` be a slicing datum of the convex planar region `D`
by the surface `F = P.carrier`: `F ∩ D` is the disjoint union of the finitely many simple closed
curves `h.c i` and the finitely many embedded arcs `h.a j`, every point of `F ∩ D` lying on one of
them (`h.covers_pt`).  Then a closed curve `γ` of `F` whose image lies in `D` has its image
contained in the image of a *single* one of these pieces.

The argument is purely topological, exactly as in the already proved spherical statement
`Work.Topology.SphereSlicing.sliceData_covers`, with the arcs added as further closed sets:
`Set.range γ.γ` is preconnected (image of the connected space `ℝ`); the ranges of the `h.c i` are
compact, hence closed (`Work.InnermostDisk.isClosed_range_closedCurve`), and so are the ranges of
the arcs (images of the compact interval `Work.Smooth.Plane.ArcInterval`); they are pairwise
disjoint by `h.disjoint`, `h.a_disjoint`, `h.a_disjoint_c`; and they cover `Set.range γ.γ` by
`h.covers_pt` and `γ.mem`.  A preconnected set covered by finitely many pairwise disjoint closed
sets lies in one of them — either apply
`Work.InnermostDisk.exists_subset_of_preconnected_iUnion` to the family indexed by `h.ι ⊕ h.κ`, or
prove the two-family version directly. -/
theorem planeSliceData_covers {P : Work.CoreTopology.ParamTorus} {D : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (h : Work.Smooth.Plane.PlaneSliceData P D) (γ : Work.CoreTopology.ClosedCurve P)
    (hγ : ∀ t : ℝ, γ.γ t ∈ D) :
    (∃ i : h.ι, Set.range γ.γ ⊆ Set.range (h.c i).γ) ∨
      (∃ j : h.κ, Set.range γ.γ ⊆ Set.range (h.a j)) := by
  classical
  -- Combine the closed components and the arcs into a single finite family indexed by
  -- `h.ι ⊕ h.κ`, as in `Work.Topology.SphereSlicing.sliceData_covers`.
  obtain ⟨k, hk⟩ := Work.InnermostDisk.exists_subset_of_preconnected_iUnion
    (isPreconnected_range γ.cont) ⟨γ.γ 0, ⟨0, rfl⟩⟩
    (fun k : h.ι ⊕ h.κ =>
      Sum.elim (fun i => Set.range (h.c i).γ) (fun j => Set.range (h.a j)) k)
    (by
      -- each member of the family is compact, hence closed
      rintro (i | j)
      · exact Work.InnermostDisk.isClosed_range_closedCurve (h.c i)
      · exact isClosed_range_arc (h.a j))
    (by
      -- distinct members of the family are disjoint
      rintro (i | i') (j | j') hne
      · exact h.disjoint (fun hh => hne (by simp [hh]))
      · exact (h.a_disjoint_c j' i).symm
      · exact h.a_disjoint_c i' j
      · exact h.a_disjoint (fun hh => hne (by simp [hh])))
    (by
      -- the family covers `Set.range γ.γ`
      rintro x ⟨t, rfl⟩
      rcases h.covers_pt (γ.γ t) (hγ t) (γ.mem t) with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact Set.mem_iUnion.mpr ⟨Sum.inl i, hi⟩
      · exact Set.mem_iUnion.mpr ⟨Sum.inr j, hj⟩)
  -- A preconnected set covered by finitely many pairwise disjoint closed sets lies in one of them.
  rcases k with i | j
  · exact Or.inl ⟨i, hk⟩
  · exact Or.inr ⟨j, hk⟩

end Work.Smooth.Plane.Slicing
