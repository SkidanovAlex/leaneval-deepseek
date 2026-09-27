import Mathlib
import Submission.Work.Whitney.PathTools.isPathConnected_sdiff_arc_empty
import Submission.Work.Whitney.PathTools.isPathConnected_sdiff_finite_of_isOpen

/-!
# The complement of a compact arc (plus a finite set) in an open path-connected set

`Work.Whitney.PathTools.isPathConnected_sdiff_arc`: if `W` is an open path-connected subset of an
`n`-dimensional topological manifold (`n ≥ 3`), `γ` is continuous and injective on `Icc 0 1` with
`γ '' Icc 0 1 ⊆ W`, and `S` is a finite subset of `W` disjoint from `γ '' Icc 0 1`, then
`W \ (γ '' Icc 0 1 ∪ S)` is path connected.

This is the relative form of the classical fact that a compact arc in a manifold of dimension
`≥ 3` does not separate it.  The main geometric input is
`Work.Whitney.PathTools.isPathConnected_sdiff_arc_empty` (the case `S = ∅`, proved from the local
room `Work.Whitney.PathTools.exists_local_room`); the finite set `S` is then removed using
`Work.Whitney.PathTools.isPathConnected_sdiff_finite_of_isOpen`.
-/

namespace Work.Whitney.PathTools

open Set Topology

theorem isPathConnected_sdiff_arc {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {W : Set M} (hW : IsOpen W) (hWc : IsPathConnected W)
    {γ : ℝ → M} (hγ : Continuous γ) (hγinj : Set.InjOn γ (Set.Icc (0:ℝ) 1))
    (hγW : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ W) (S : Set M) (hS : S.Finite)
    (hSW : S ⊆ W) (hSdisj : Disjoint S (γ '' Set.Icc (0:ℝ) 1)) :
    IsPathConnected (W \ (γ '' Set.Icc (0:ℝ) 1 ∪ S)) := by
  have hO : IsOpen (W \ γ '' Set.Icc (0:ℝ) 1) :=
    hW.sdiff (isCompact_Icc.image hγ).isClosed
  have hOc : IsPathConnected (W \ γ '' Set.Icc (0:ℝ) 1) :=
    isPathConnected_sdiff_arc_empty hn hW hWc hγ hγinj hγW
  have hSO : S ⊆ W \ γ '' Set.Icc (0:ℝ) 1 := fun x hx =>
    ⟨hSW hx, fun hc => hSdisj.le_bot ⟨hx, hc⟩⟩
  have hres := isPathConnected_sdiff_finite_of_isOpen (n := n) (by omega) hO hOc hS hSO
  rwa [Set.sdiff_sdiff] at hres

end Work.Whitney.PathTools
