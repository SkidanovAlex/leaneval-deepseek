import Mathlib
import Submission.Work.Whitney.PathTools.isPathConnected_sdiff_arc
import Submission.Work.Whitney.PathTools.arc_nonseparates_open_surface
import Submission.Work.Whitney.PathTools.isPathConnected_sdiff_finite_of_isOpen

/-!
# Removing finitely many pairwise disjoint arcs (and finitely many points) from an open
path connected subset of a topological `n`-manifold, `n ≥ 2`

Main result `Work.Noncompact.CompressionTube.isPathConnected_sdiff_iUnion_arcs_finite`: if `W` is
an open path connected subset of a topological `n`-manifold (`n ≥ 2`), `ι` is finite, each
`γ i : ℝ → M` is continuous and injective on `[0,1]` with image in `W`, these images are pairwise
disjoint, and `F ⊆ W` is a finite set disjoint from `⋃ i, γ i '' [0,1]`, then
`W \ ((⋃ i, γ i '' [0,1]) ∪ F)` is path connected.

The argument is a two-stage induction.

* A *single* compact arc is removed by `isPathConnected_sdiff_arc_removal`: for `n ≥ 3` this is the
  classical statement that a compact arc does not separate a manifold of dimension `≥ 3`
  (`Work.Whitney.PathTools.isPathConnected_sdiff_arc_empty`); for `n = 2` it is the surface
  theorem `Work.Whitney.PathTools.arc_nonseparates_open_surface`.

* A finite family of *pairwise disjoint* arcs is then removed one at a time (Finset induction),
  using that after removing some arcs the remaining ones still lie in the (still open, still path
  connected) complement.

* Finally the finite set `F` is removed with
  `Work.Whitney.PathTools.isPathConnected_sdiff_finite_of_isOpen`.
-/

set_option linter.style.haveILetI false

namespace Work.Noncompact.CompressionTube

open Set Topology

/-- **Removing one compact arc.**  If `W` is an open path connected subset of an `n`-manifold
(`n ≥ 2`) and the image of `γ '' [0,1]` is a compact arc lying in `W`, then `W` minus that arc is
still path connected. -/
theorem isPathConnected_sdiff_arc_removal {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {W : Set M} (hW : IsOpen W) (hWc : IsPathConnected W)
    {γ : ℝ → M} (hγ : Continuous γ) (hγinj : Set.InjOn γ (Set.Icc (0:ℝ) 1))
    (hγW : γ '' Set.Icc (0:ℝ) 1 ⊆ W) :
    IsPathConnected (W \ γ '' Set.Icc (0:ℝ) 1) := by
  rcases lt_or_eq_of_le hn with h3 | h2
  · exact Work.Whitney.PathTools.isPathConnected_sdiff_arc_empty h3 hW hWc hγ hγinj
      (fun t ht => hγW ⟨t, ht, rfl⟩)
  · subst h2
    exact Work.Whitney.PathTools.arc_nonseparates_open_surface hW hWc.isConnected.2 hγ hγinj
      (fun t ht => hγW ⟨t, ht, rfl⟩)

theorem isPathConnected_sdiff_iUnion_arcs_finite {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {W : Set M} (hW : IsOpen W) (hWc : IsPathConnected W)
    {ι : Type*} [Finite ι] {γ : ι → ℝ → M} (hγ : ∀ i, Continuous (γ i))
    (hγinj : ∀ i, Set.InjOn (γ i) (Set.Icc (0:ℝ) 1))
    (hγW : ∀ i, γ i '' Set.Icc (0:ℝ) 1 ⊆ W)
    (hdisj : ∀ i j, i ≠ j → Disjoint (γ i '' Set.Icc (0:ℝ) 1) (γ j '' Set.Icc (0:ℝ) 1))
    {F : Set M} (hF : F.Finite) (hFW : F ⊆ W)
    (hFdisj : Disjoint F (⋃ i, γ i '' Set.Icc (0:ℝ) 1)) :
    IsPathConnected (W \ ((⋃ i, γ i '' Set.Icc (0:ℝ) 1) ∪ F)) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  -- Stage 2: remove the finitely many pairwise disjoint arcs, one at a time.
  have key : ∀ s : Finset ι, IsPathConnected (W \ ⋃ i ∈ s, γ i '' Set.Icc (0:ℝ) 1) := by
    intro s
    induction s using Finset.induction with
    | empty => simpa using hWc
    | insert a s ha ih =>
      rw [Finset.set_biUnion_insert]
      have hclosed : IsClosed (⋃ i ∈ s, γ i '' Set.Icc (0:ℝ) 1) :=
        isClosed_biUnion_finset fun i _ => (isCompact_Icc.image (hγ i)).isClosed
      have hsub : γ a '' Set.Icc (0:ℝ) 1 ⊆ W \ ⋃ i ∈ s, γ i '' Set.Icc (0:ℝ) 1 := by
        rintro x ⟨t, ht, rfl⟩
        refine ⟨hγW a ⟨t, ht, rfl⟩, ?_⟩
        intro hx
        rcases Set.mem_iUnion₂.mp hx with ⟨i, his, hxi⟩
        exact (Set.disjoint_left.mp (hdisj a i (fun h => ha (h ▸ his)))) ⟨t, ht, rfl⟩ hxi
      have hfin := isPathConnected_sdiff_arc_removal hn (hW.sdiff hclosed) ih
        (hγ a) (hγinj a) hsub
      rw [Set.sdiff_sdiff, Set.union_comm] at hfin
      exact hfin
  have huniv : (⋃ i, γ i '' Set.Icc (0:ℝ) 1)
      = ⋃ i ∈ (Finset.univ : Finset ι), γ i '' Set.Icc (0:ℝ) 1 := by
    ext x; simp
  have hUclosed : IsClosed (⋃ i, γ i '' Set.Icc (0:ℝ) 1) := by
    rw [huniv]
    exact isClosed_biUnion_finset fun i _ => (isCompact_Icc.image (hγ i)).isClosed
  have hkey := key Finset.univ
  rw [← huniv] at hkey
  -- Stage 3: remove the finite set.
  have hFO : F ⊆ W \ ⋃ i, γ i '' Set.Icc (0:ℝ) 1 :=
    fun x hx => ⟨hFW hx, fun hc => hFdisj.le_bot ⟨hx, hc⟩⟩
  have hres := Work.Whitney.PathTools.isPathConnected_sdiff_finite_of_isOpen hn
    (hW.sdiff hUclosed) hkey hF hFO
  rwa [Set.sdiff_sdiff] at hres

end Work.Noncompact.CompressionTube
