import Mathlib
import Submission.Work.Whitney.PathTools.isPathConnected_sdiff_arc_empty
import Submission.Work.Whitney.PathTools.isPathConnected_sdiff_finite_of_isOpen
import Submission.Work.Whitney.PathTools.isPathConnected_compl_finite

/-!
# The complement of an arc together with finitely many points

`Work.Whitney.PathTools.isPathConnected_compl_arc_union_finite`: in a connected topological
`n`-manifold with `n ≥ 3`, the complement of the union of an arc and a finite set is path
connected.

The proof is an assembly of already-proven pieces.

* `M` is a charted space, hence locally path connected, and being connected it is path connected;
  so the ambient space is an open path connected set `W = univ`.
* `isPathConnected_sdiff_arc_empty` removes the arc `γ '' [0,1]` from `M` (the case of an empty
  finite set).
* The complement `(γ '' [0,1])ᶜ` is open and path connected, so
  `isPathConnected_sdiff_finite_of_isOpen` removes the remaining finite set
  `S \ γ '' [0,1]`; the union `γ '' [0,1] ∪ (S \ γ '' [0,1])` is `γ '' [0,1] ∪ S`.
-/

open Set Topology

namespace Work.Whitney.PathTools

theorem isPathConnected_compl_arc_union_finite {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {γ : ℝ → M} (hγ : Continuous γ) (hγinj : Set.InjOn γ (Set.Icc (0:ℝ) 1))
    (S : Set M) (hS : S.Finite) :
    IsPathConnected ((γ '' Set.Icc (0:ℝ) 1 ∪ S)ᶜ : Set M) := by
  haveI : LocallyPathConnectedSpace M := locallyPathConnectedSpace_chartedSpace (n := n)
  haveI : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  have hclosed : IsClosed (γ '' Set.Icc (0:ℝ) 1) :=
    (isCompact_Icc.image hγ).isClosed
  -- Step 1: remove the arc.
  have harc : IsPathConnected ((γ '' Set.Icc (0:ℝ) 1)ᶜ : Set M) := by
    have h := isPathConnected_sdiff_arc_empty (n := n) hn (W := univ) isOpen_univ
      isPathConnected_univ hγ hγinj (fun t _ => Set.mem_univ _)
    simpa only [Set.compl_eq_univ_sdiff] using h
  -- Step 2: remove the remaining finite points, which live inside the (open) complement.
  have hfin : IsPathConnected (((γ '' Set.Icc (0:ℝ) 1)ᶜ : Set M) \
      (S \ γ '' Set.Icc (0:ℝ) 1)) :=
    isPathConnected_sdiff_finite_of_isOpen (n := n) (M := M) (by omega)
      hclosed.isOpen_compl harc (F := S \ γ '' Set.Icc (0:ℝ) 1) (hS.sdiff)
      (fun x hx => hx.2)
  have hset : ((γ '' Set.Icc (0:ℝ) 1)ᶜ : Set M) \ (S \ γ '' Set.Icc (0:ℝ) 1)
      = (γ '' Set.Icc (0:ℝ) 1 ∪ S)ᶜ := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      rintro (h | h)
      · exact hx1 h
      · exact hx2 ⟨h, hx1⟩
    · intro hx
      exact ⟨fun h => hx (Or.inl h), fun h => hx (Or.inr h.1)⟩
  rwa [hset] at hfin

end Work.Whitney.PathTools
