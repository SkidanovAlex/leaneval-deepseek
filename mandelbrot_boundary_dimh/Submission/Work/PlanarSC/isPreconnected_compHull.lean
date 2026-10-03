import Mathlib
import Submission.Work.PlanarSC.HullDefs
import Submission.Work.PlanarSC.frontier_componentIn_compl_subset
import Submission.Work.PlanarSC.nonempty_inter_closure_componentIn

/-!
# The hull of a preconnected polyomino is preconnected

The main content is the general statement `isPreconnected_compHull_of_isClosed`: for a closed,
nonempty, preconnected `A ⊆ ℂ` the "filled-in" set `compHull A` (the set of points whose component
in `Aᶜ` is bounded) is again preconnected.

The point is that `compHull A` is the union of `A` with the closures of the components of `Aᶜ`
lying in it:
* a component `Z` of `Aᶜ` has `frontier Z ⊆ A` (`Work.PlanarSC.frontier_componentIn_compl_subset`),
  so `closure Z ⊆ Z ∪ A`;
* a nonempty component `Z = connectedComponentIn Aᶜ x` with `x ∉ A` always has
  `A ∩ closure Z ≠ ∅` (`Work.PlanarSC.nonempty_inter_closure_componentIn`).

Hence every `A ∪ closure Z` is preconnected (a union of two preconnected sets with nonempty
intersection), and `compHull A` is the union of the sets `A ∪ closure (connectedComponentIn Aᶜ x)`
over `x ∈ compHull A`, which are pairwise intersecting in `A ≠ ∅`.
-/

open Set

namespace Work.PlanarSC

/-- A dyadic polyomino is closed (it is a finite union of closed squares). -/
theorem isClosed_dyadicPolyomino (n : ℕ) (S : Finset (ℤ × ℤ)) :
    IsClosed (dyadicPolyomino n S) :=
  isClosed_biUnion_finset (fun p _ => Commons.Topology.Plane.isClosed_dSq n p)

/-- The closure of a connected component of the complement of a closed set `A ⊆ ℂ` is contained in
that component together with `A`. -/
theorem closure_componentIn_subset {A : Set ℂ} (hAcl : IsClosed A) (x : ℂ) :
    closure (connectedComponentIn Aᶜ x) ⊆ connectedComponentIn Aᶜ x ∪ A := by
  by_cases hxA : x ∈ A
  · have hZ : connectedComponentIn Aᶜ x = ∅ := connectedComponentIn_eq_empty (by simpa using hxA)
    rw [hZ, closure_empty]
    exact Set.empty_subset _
  · have hZopen : IsOpen (connectedComponentIn Aᶜ x) := hAcl.isOpen_compl.connectedComponentIn
    have hfr : frontier (connectedComponentIn Aᶜ x) ⊆ A :=
      frontier_componentIn_compl_subset hAcl x
    rw [closure_eq_interior_union_frontier, hZopen.interior_eq]
    exact union_subset_union_right _ hfr

/-- **The hull of a closed, nonempty, preconnected subset of `ℂ` is preconnected.**

`compHull A` is the union of the preconnected sets `A ∪ closure (connectedComponentIn Aᶜ x)` over
`x ∈ compHull A`; each of them is preconnected because `A` is preconnected, `closure Z` is
preconnected and `A ∩ closure Z ≠ ∅`, and they all contain the nonempty set `A`. -/
theorem isPreconnected_compHull_of_isClosed {A : Set ℂ} (hAcl : IsClosed A) (hne : A.Nonempty)
    (hpre : IsPreconnected A) : IsPreconnected (compHull A) := by
  -- each `A ∪ closure Z` is contained in the hull
  have hsub : ∀ x : ℂ, x ∈ compHull A →
      A ∪ closure (connectedComponentIn Aᶜ x) ⊆ compHull A := by
    intro x hx
    apply union_subset subset_compHull
    intro y hy
    rcases closure_componentIn_subset hAcl x hy with h | h
    · rw [mem_compHull, ← connectedComponentIn_eq h]
      exact hx
    · exact subset_compHull h
  -- the hull is the union of these sets
  have hunion : compHull A =
      ⋃ x : {x : ℂ // x ∈ compHull A}, (A ∪ closure (connectedComponentIn Aᶜ x.1)) := by
    ext y
    constructor
    · intro hy
      refine mem_iUnion.mpr ⟨⟨y, hy⟩, ?_⟩
      by_cases hyA : y ∈ A
      · exact Or.inl hyA
      · exact Or.inr (subset_closure (mem_connectedComponentIn (by simpa using hyA)))
    · intro hy
      obtain ⟨x, hx⟩ := mem_iUnion.mp hy
      exact hsub x.1 x.2 hx
  rw [hunion]
  refine isPreconnected_iUnion ?_ ?_
  · obtain ⟨a, ha⟩ := hne
    exact ⟨a, mem_iInter.mpr (fun _ => Or.inl ha)⟩
  · intro x
    by_cases hxA : x.1 ∈ A
    · have hZ : connectedComponentIn Aᶜ x.1 = ∅ :=
        connectedComponentIn_eq_empty (by simpa using hxA)
      have : A ∪ closure (connectedComponentIn Aᶜ x.1) = A := by rw [hZ, closure_empty, union_empty]
      rw [this]
      exact hpre
    · refine IsPreconnected.union' ?_ hpre isPreconnected_connectedComponentIn.closure
      exact nonempty_inter_closure_componentIn hAcl hne hxA

/-- The hull of a nonempty preconnected polyomino is preconnected: a bounded component `Z` of the
complement meets the polyomino in its closure (`frontier Z ⊆ A`), so `A ∪ closure Z` is
preconnected, and the hull is the union of these over the components. -/
theorem isPreconnected_compHull (n : ℕ) (S : Finset (ℤ × ℤ))
    (hne : (dyadicPolyomino n S).Nonempty) (hpre : IsPreconnected (dyadicPolyomino n S)) :
    IsPreconnected (compHull (dyadicPolyomino n S)) :=
  isPreconnected_compHull_of_isClosed (isClosed_dyadicPolyomino n S) hne hpre

end Work.PlanarSC
