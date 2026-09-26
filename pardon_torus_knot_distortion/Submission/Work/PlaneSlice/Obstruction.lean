import Submission.Work.PlaneSlice.SliceConstruction

/-!
# Why the transversality predicate is too strong for the slice of an **open** box

`Work.Smooth.Plane.TransversePlane P D` requires the family of arcs describing `F ∩ D` to consist
of *closed* arcs whose image lies in `D` (and the family is finite).  Since the family covers
`F ∩ D` and each of its members is compact, the union of the family is a compact — in particular
closed — subset of `D` which contains `F ∩ D`.  Hence:

> if `D` is in general position with respect to `F` in the sense of `TransversePlane`, then the
> closure of `D ∩ F` is still contained in `D`.

This file records the two equivalent forms of that observation.  It is the reason why the
transversality of the **slice of Pardon's open box**,
`Work.BoxShrink.Core.cutDisc s c σ u = Submission.PBox s c σ ∩ {y | y (σ 2) = c (σ 2) + u}`, cannot
hold once a circle of `F ∩ {plane}` crosses the boundary of the open box: the crossing point is a
point of `F ∩ ∂PBox` which is a limit of points of `F ∩ PBox` but does not belong to the open box.
See `Submission/Work/PlaneSlice/README.md` for the explicit numerical example (the standard torus
`(ρ - 2)² + z² = 1`, the box `s = 5/2`, centre `0`, the coordinate plane `z = u` with `|u| ≤ √3/2`).

## Main results

* `Work.PlaneSlice.closure_inter_subset_of_transversePlane` — `TransversePlane P D` implies
  `closure (D ∩ P.carrier) ⊆ D`;
* `Work.PlaneSlice.not_transversePlane_of_exists_closure_notMem` — the contrapositive, in the form
  in which a concrete counterexample is checked.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.PlaneSlice

noncomputable section

/-- **The trace of the surface in a transversally-cut region accumulates only inside the region.**

If `D` is in general position with respect to `F = P.carrier` (`Work.Smooth.Plane.TransversePlane`),
then `F ∩ D` is covered by finitely many compact pieces lying in `D`, so its closure is contained in
`D`.  This is the formal obstruction to the transversality of the slice of an *open* region. -/
theorem closure_inter_subset_of_transversePlane {P : Work.CoreTopology.ParamTorus} {D : Set R3}
    (h : Work.Smooth.Plane.TransversePlane P D) : closure (D ∩ P.carrier) ⊆ D := by
  obtain ⟨ι, hι, c, κ, hκ, a, hsimple, hdisj, hmem, ha_inj, ha_mem, ha_surf, ha_disj,
    ha_disj_c, hcov⟩ := h
  haveI := hι
  haveI := hκ
  have hcompact : IsCompact ((⋃ i : ι, Set.range (c i).γ) ∪ ⋃ j : κ, Set.range (a j)) :=
    (isCompact_iUnion fun i => isCompact_range_closedCurve (c i)).union
      (isCompact_iUnion fun j => isCompact_range (a j).continuous)
  have hsub : D ∩ P.carrier ⊆ (⋃ i : ι, Set.range (c i).γ) ∪ ⋃ j : κ, Set.range (a j) := by
    rintro x ⟨hxD, hxC⟩
    rcases hcov x hxD hxC with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact Or.inl (Set.mem_iUnion.mpr ⟨i, hi⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨j, hj⟩)
  have hsubD : (⋃ i : ι, Set.range (c i).γ) ∪ ⋃ j : κ, Set.range (a j) ⊆ D := by
    rintro x (hx | hx)
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨t, ht⟩ := hi
      rw [← ht]
      exact hmem i t
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      obtain ⟨s, hs⟩ := hj
      rw [← hs]
      exact ha_mem j s
  calc closure (D ∩ P.carrier) ⊆ closure ((⋃ i : ι, Set.range (c i).γ) ∪
        ⋃ j : κ, Set.range (a j)) := closure_mono hsub
    _ = (⋃ i : ι, Set.range (c i).γ) ∪ ⋃ j : κ, Set.range (a j) := hcompact.isClosed.closure_eq
    _ ⊆ D := hsubD

/-- **The contrapositive of `closure_inter_subset_of_transversePlane`**: to refute the
transversality of `D` it suffices to exhibit a point of the surface which is a limit of points of
`F ∩ D` and does not lie in `D`.

This is the form in which the failure of the transversality of the slice of Pardon's *open* box is
verified: a circle of `F ∩ {plane}` crossing the boundary of the box provides such a point at every
plane level `u` for which the crossing occurs. -/
theorem not_transversePlane_of_exists_closure_notMem {P : Work.CoreTopology.ParamTorus} {D : Set R3}
    (h : ∃ x ∈ P.carrier, x ∈ closure (D ∩ P.carrier) ∧ x ∉ D) :
    ¬ Work.Smooth.Plane.TransversePlane P D := fun hT => by
  obtain ⟨x, -, hxcl, hxnot⟩ := h
  exact hxnot (closure_inter_subset_of_transversePlane hT hxcl)

/-! ## The pieces of a transversality witness are forced

The family of a `Work.Smooth.Plane.TransversePlane` witness is *not* arbitrary: the union of its
pieces is `D ∩ F` and the pieces are pairwise disjoint and closed, so a connected subset of `D ∩ F`
which meets a piece is *contained* in it — the pieces are exactly the connected components of
`D ∩ F`.  This is the combinatorial half of the discussion in `Submission/Work/PlaneSlice/README.md`
(§3.2): what the axioms of `TransversePlane` do *not* determine is the choice of the disc bounded by
each circle piece, which is why `covers_interior` is not derivable from them alone. -/

/-- **A preconnected subset of a finite disjoint union of closed sets is contained in every member it
meets.** -/
theorem preconnected_subset_piece {X : Type*} [TopologicalSpace X] {σ : Type} [Fintype σ]
    {S : σ → Set X} (hclosed : ∀ s, IsClosed (S s))
    (hdisj : Pairwise fun s t => Disjoint (S s) (S t)) {K : Set X} (hKp : IsPreconnected K)
    (hKne : K.Nonempty) (hKsub : K ⊆ ⋃ s, S s) {s : σ} (hmeet : (K ∩ S s).Nonempty) :
    K ⊆ S s := by
  obtain ⟨s₀, hs₀⟩ := Work.InnermostDisk.exists_subset_of_preconnected_iUnion hKp hKne S hclosed
    hdisj hKsub
  obtain ⟨x, hxK, hxS⟩ := hmeet
  have h1 : x ∈ S s₀ := hs₀ hxK
  have h2 : s = s₀ := by
    by_contra hne
    exact (Set.disjoint_left.mp (hdisj hne) hxS) h1
  rwa [h2]

end

end Work.PlaneSlice
