import Mathlib
import Submission.Work.Whitney.PathTools.arc_nonseparates_open_surface
import Submission.Work.Whitney.PathTools.isPathConnected_sdiff_arc_empty
import Submission.Work.Whitney.PathTools.isPathConnected_sdiff_finite_of_isOpen

/-!
# Removing finitely many disjoint arcs (and finitely many points) from an open
preconnected set of an `n`-manifold, `n ≥ 2`.

`Work.Noncompact.Routing.isPreconnected_sdiff_iUnion_image_arcs`: the complement of a finite
union of pairwise disjoint arcs in an open preconnected `C ⊆ M` is preconnected
(`n ≥ 2`).  The proof removes the arcs one at a time, using

* `Work.Whitney.PathTools.arc_nonseparates_open_surface` for `n = 2`,
* `Work.Whitney.PathTools.isPathConnected_sdiff_arc_empty` for `3 ≤ n`,

and finishes with `Work.Whitney.PathTools.isPathConnected_sdiff_finite_of_isOpen` to remove a
finite set.  This is the form needed by the shell-by-shell routing of
`Submission/Work/Noncompact/Routing/NOTES_canals.md`.
-/

namespace Work.Noncompact.Routing

open Set Topology

/-- **One arc does not separate an open preconnected set of an `n`-manifold, `n ≥ 2`.** -/
theorem isPreconnected_sdiff_image_arc {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {C : Set M} (hC : IsOpen C) (hCc : IsPreconnected C) {γ : ℝ → M} (hγ : Continuous γ)
    (hinj : Set.InjOn γ (Set.Icc (0:ℝ) 1)) (hγC : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ C) :
    IsPreconnected (C \ γ '' Set.Icc (0:ℝ) 1) := by
  by_cases hne : (C \ γ '' Set.Icc (0:ℝ) 1).Nonempty
  · rcases eq_or_lt_of_le hn with h2 | h3
    · subst h2
      exact (Work.Whitney.PathTools.arc_nonseparates_open_surface (M := M) hC hCc hγ hinj
        hγC).isConnected.isPreconnected
    · haveI : LocallyPathConnectedSpace M :=
        Work.Whitney.PathTools.locallyPathConnectedSpace_chartedSpace (n := n)
      have hCne : C.Nonempty := ⟨hne.some, hne.some_mem.1⟩
      have hCpc : IsPathConnected C := hC.isConnected_iff_isPathConnected.mp ⟨hCne, hCc⟩
      exact (Work.Whitney.PathTools.isPathConnected_sdiff_arc_empty (n := n) h3 hC hCpc hγ hinj hγC).isConnected.isPreconnected
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    exact isPreconnected_empty

/-- **Finite unions of pairwise disjoint arcs do not separate.**
`C` open preconnected in an `n`-manifold (`n ≥ 2`), `γ i` arcs with pairwise disjoint images
inside `C`; then `C \ ⋃ i, γ i '' [0,1]` is preconnected. -/
theorem isPreconnected_sdiff_iUnion_image_arcs {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    ∀ (k : ℕ) {γ : Fin k → ℝ → M}, (∀ i, Continuous (γ i)) →
      (∀ i, Set.InjOn (γ i) (Set.Icc (0:ℝ) 1)) →
      ∀ {C : Set M}, IsOpen C → IsPreconnected C →
      (∀ i t, t ∈ Set.Icc (0:ℝ) 1 → γ i t ∈ C) →
      (∀ i j, i ≠ j → Disjoint (γ i '' Set.Icc (0:ℝ) 1) (γ j '' Set.Icc (0:ℝ) 1)) →
      IsPreconnected (C \ ⋃ i, γ i '' Set.Icc (0:ℝ) 1) := by
  intro k
  induction k with
  | zero =>
    intro γ _ _ C _ hCc _ _
    simpa using hCc
  | succ k ih =>
    intro γ hγc hγinj C hC hCc hγC hγdisj
    have hC' : IsPreconnected (C \ γ 0 '' Set.Icc (0:ℝ) 1) :=
      isPreconnected_sdiff_image_arc hn hC hCc (hγc 0) (hγinj 0) (hγC 0)
    have hOpen' : IsOpen (C \ γ 0 '' Set.Icc (0:ℝ) 1) :=
      hC.sdiff (isCompact_Icc.image (hγc 0)).isClosed
    have hγ'c : ∀ i : Fin k, Continuous (γ i.succ) := fun i => hγc i.succ
    have hγ'inj : ∀ i : Fin k, Set.InjOn (γ i.succ) (Set.Icc (0:ℝ) 1) := fun i => hγinj i.succ
    have hγ'C : ∀ (i : Fin k) t, t ∈ Set.Icc (0:ℝ) 1 →
        γ i.succ t ∈ C \ γ 0 '' Set.Icc (0:ℝ) 1 := by
      intro i t ht
      refine ⟨hγC i.succ t ht, ?_⟩
      intro hcon
      have hdisj := hγdisj i.succ 0 (Fin.succ_ne_zero i)
      exact Set.disjoint_left.mp hdisj ⟨t, ht, rfl⟩ hcon
    have hγ'disj : ∀ i j : Fin k, i ≠ j →
        Disjoint (γ i.succ '' Set.Icc (0:ℝ) 1) (γ j.succ '' Set.Icc (0:ℝ) 1) := by
      intro i j hij
      exact hγdisj i.succ j.succ (fun h => hij (Fin.succ_injective k h))
    have hmain : IsPreconnected ((C \ γ 0 '' Set.Icc (0:ℝ) 1) \
        ⋃ i : Fin k, γ i.succ '' Set.Icc (0:ℝ) 1) :=
      ih hγ'c hγ'inj hOpen' hC' hγ'C hγ'disj
    rw [Set.iUnion_fin_add_one_eq_iUnion_succ (fun i => γ i '' Set.Icc (0:ℝ) 1)]
    simp only [Function.comp_def]
    have heq : C \ (γ 0 '' Set.Icc (0:ℝ) 1 ∪ ⋃ i : Fin k, γ i.succ '' Set.Icc (0:ℝ) 1)
        = (C \ γ 0 '' Set.Icc (0:ℝ) 1) \ ⋃ i : Fin k, γ i.succ '' Set.Icc (0:ℝ) 1 := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_union, Set.mem_iUnion]
      tauto
    rw [heq]
    exact hmain

/-- **Either/or form.**  As `isPreconnected_sdiff_iUnion_image_arcs`, but each arc only has to
be either inside `C` (then it is removed) or disjoint from `C` (then it is irrelevant).  This is
the form used by the shell routing: the walls are connected, so each of them is either contained
in the component of the point being routed or disjoint from it. -/
theorem isPreconnected_sdiff_iUnion_image_arcs_or {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    ∀ (k : ℕ) {γ : Fin k → ℝ → M}, (∀ i, Continuous (γ i)) →
      (∀ i, Set.InjOn (γ i) (Set.Icc (0:ℝ) 1)) →
      ∀ {C : Set M}, IsOpen C → IsPreconnected C →
      (∀ i, γ i '' Set.Icc (0:ℝ) 1 ⊆ C ∨ Disjoint (γ i '' Set.Icc (0:ℝ) 1) C) →
      (∀ i j, i ≠ j → Disjoint (γ i '' Set.Icc (0:ℝ) 1) (γ j '' Set.Icc (0:ℝ) 1)) →
      IsPreconnected (C \ ⋃ i, γ i '' Set.Icc (0:ℝ) 1) := by
  intro k
  induction k with
  | zero =>
    intro γ _ _ C _ hCc _ _
    simpa using hCc
  | succ k ih =>
    intro γ hγc hγinj C hC hCc hγC hγdisj
    have hγ'c : ∀ i : Fin k, Continuous (γ i.succ) := fun i => hγc i.succ
    have hγ'inj : ∀ i : Fin k, Set.InjOn (γ i.succ) (Set.Icc (0:ℝ) 1) := fun i => hγinj i.succ
    have hγ'disj : ∀ i j : Fin k, i ≠ j →
        Disjoint (γ i.succ '' Set.Icc (0:ℝ) 1) (γ j.succ '' Set.Icc (0:ℝ) 1) := fun i j hij =>
      hγdisj i.succ j.succ (fun h => hij (Fin.succ_injective k h))
    rcases hγC 0 with h0sub | h0disj
    · have hC' : IsPreconnected (C \ γ 0 '' Set.Icc (0:ℝ) 1) :=
        isPreconnected_sdiff_image_arc hn hC hCc (hγc 0) (hγinj 0)
          (fun t ht => h0sub ⟨t, ht, rfl⟩)
      have hOpen' : IsOpen (C \ γ 0 '' Set.Icc (0:ℝ) 1) :=
        hC.sdiff (isCompact_Icc.image (hγc 0)).isClosed
      have hγ'C : ∀ i : Fin k, γ i.succ '' Set.Icc (0:ℝ) 1 ⊆ C \ γ 0 '' Set.Icc (0:ℝ) 1 ∨
          Disjoint (γ i.succ '' Set.Icc (0:ℝ) 1) (C \ γ 0 '' Set.Icc (0:ℝ) 1) := by
        intro i
        rcases hγC i.succ with hsub | hdis
        · left
          intro x hx
          exact ⟨hsub hx, fun hcon =>
            Set.disjoint_left.mp (hγdisj i.succ 0 (Fin.succ_ne_zero i)) hx hcon⟩
        · right
          exact Disjoint.mono_right Set.diff_subset hdis
      have hmain := ih hγ'c hγ'inj hOpen' hC' hγ'C hγ'disj
      rw [Set.iUnion_fin_add_one_eq_iUnion_succ (fun i => γ i '' Set.Icc (0:ℝ) 1)]
      simp only [Function.comp_def]
      have heq : C \ (γ 0 '' Set.Icc (0:ℝ) 1 ∪ ⋃ i : Fin k, γ i.succ '' Set.Icc (0:ℝ) 1)
          = (C \ γ 0 '' Set.Icc (0:ℝ) 1) \ ⋃ i : Fin k, γ i.succ '' Set.Icc (0:ℝ) 1 := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_union, Set.mem_iUnion]
        tauto
      rw [heq]
      exact hmain
    · have hγ'C : ∀ i : Fin k, γ i.succ '' Set.Icc (0:ℝ) 1 ⊆ C ∨
          Disjoint (γ i.succ '' Set.Icc (0:ℝ) 1) C := fun i => hγC i.succ
      have hmain := ih hγ'c hγ'inj hC hCc hγ'C hγ'disj
      rw [Set.iUnion_fin_add_one_eq_iUnion_succ (fun i => γ i '' Set.Icc (0:ℝ) 1)]
      simp only [Function.comp_def]
      have heq : C \ (γ 0 '' Set.Icc (0:ℝ) 1 ∪ ⋃ i : Fin k, γ i.succ '' Set.Icc (0:ℝ) 1)
          = C \ ⋃ i : Fin k, γ i.succ '' Set.Icc (0:ℝ) 1 := by
        ext x
        simp only [Set.mem_sdiff, Set.mem_union, Set.mem_iUnion]
        constructor
        · rintro ⟨hxC, hnot⟩
          exact ⟨hxC, fun ⟨i, hi⟩ => hnot (Or.inr ⟨i, hi⟩)⟩
        · rintro ⟨hxC, hnot⟩
          exact ⟨hxC, fun h => h.elim (fun h0 => (Set.disjoint_left.mp h0disj h0) hxC)
            (fun h => hnot h)⟩
      rw [heq]
      exact hmain

/-- **Either/or form, arbitrary finite index type.** -/
theorem isPreconnected_sdiff_iUnion_image_arcs_or' {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {ι : Type*} [Fintype ι] {γ : ι → ℝ → M} (hγc : ∀ i, Continuous (γ i))
    (hγinj : ∀ i, Set.InjOn (γ i) (Set.Icc (0:ℝ) 1))
    {C : Set M} (hC : IsOpen C) (hCc : IsPreconnected C)
    (hγC : ∀ i, γ i '' Set.Icc (0:ℝ) 1 ⊆ C ∨ Disjoint (γ i '' Set.Icc (0:ℝ) 1) C)
    (hγdisj : ∀ i j, i ≠ j → Disjoint (γ i '' Set.Icc (0:ℝ) 1) (γ j '' Set.Icc (0:ℝ) 1)) :
    IsPreconnected (C \ ⋃ i, γ i '' Set.Icc (0:ℝ) 1) := by
  classical
  obtain ⟨e⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := ⟨Fintype.equivFin ι⟩
  have hmain := isPreconnected_sdiff_iUnion_image_arcs_or hn (Fintype.card ι)
    (fun i : Fin (Fintype.card ι) => hγc (e.symm i))
    (fun i => hγinj (e.symm i))
    hC hCc (fun i => hγC (e.symm i))
    (fun i j hij => hγdisj (e.symm i) (e.symm j) (fun h => hij (e.symm.injective h)))
  have heq : ⋃ i : Fin (Fintype.card ι), γ (e.symm i) '' Set.Icc (0:ℝ) 1
      = ⋃ i : ι, γ i '' Set.Icc (0:ℝ) 1 := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e.symm i, hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨e i, by simpa using hi⟩
  rw [heq] at hmain
  exact hmain

/-- **Finite unions of pairwise disjoint arcs plus a finite set do not separate.** -/
theorem isPreconnected_sdiff_iUnion_image_arcs_union_finite {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {k : ℕ} {γ : Fin k → ℝ → M} (hγc : ∀ i, Continuous (γ i))
    (hγinj : ∀ i, Set.InjOn (γ i) (Set.Icc (0:ℝ) 1))
    {C : Set M} (hC : IsOpen C) (hCc : IsPreconnected C)
    (hγC : ∀ i t, t ∈ Set.Icc (0:ℝ) 1 → γ i t ∈ C)
    (hγdisj : ∀ i j, i ≠ j → Disjoint (γ i '' Set.Icc (0:ℝ) 1) (γ j '' Set.Icc (0:ℝ) 1))
    {F : Set M} (hFfin : F.Finite) (hFC : F ⊆ C) :
    IsPreconnected (C \ ((⋃ i, γ i '' Set.Icc (0:ℝ) 1) ∪ F)) := by
  have harcs : IsPreconnected (C \ ⋃ i, γ i '' Set.Icc (0:ℝ) 1) :=
    isPreconnected_sdiff_iUnion_image_arcs hn k hγc hγinj hC hCc hγC hγdisj
  have hclosed : IsClosed (⋃ i, γ i '' Set.Icc (0:ℝ) 1) :=
    (isCompact_iUnion (fun i => isCompact_Icc.image (hγc i))).isClosed
  by_cases hne : (C \ ⋃ i, γ i '' Set.Icc (0:ℝ) 1).Nonempty
  · haveI : LocallyPathConnectedSpace M :=
      Work.Whitney.PathTools.locallyPathConnectedSpace_chartedSpace (n := n)
    have hOpen₁ : IsOpen (C \ ⋃ i, γ i '' Set.Icc (0:ℝ) 1) := hC.sdiff hclosed
    have hpc₁ : IsPathConnected (C \ ⋃ i, γ i '' Set.Icc (0:ℝ) 1) :=
      hOpen₁.isConnected_iff_isPathConnected.mp ⟨hne, harcs⟩
    have hfin : (F ∩ (C \ ⋃ i, γ i '' Set.Icc (0:ℝ) 1)).Finite := hFfin.inter_of_left _
    have hsub : F ∩ (C \ ⋃ i, γ i '' Set.Icc (0:ℝ) 1)
        ⊆ (C \ ⋃ i, γ i '' Set.Icc (0:ℝ) 1) := inter_subset_right
    have hres := Work.Whitney.PathTools.isPathConnected_sdiff_finite_of_isOpen hn hOpen₁ hpc₁
      hfin hsub
    have heq : (C \ ⋃ i, γ i '' Set.Icc (0:ℝ) 1) \
          (F ∩ (C \ ⋃ i, γ i '' Set.Icc (0:ℝ) 1)) = C \ ((⋃ i, γ i '' Set.Icc (0:ℝ) 1) ∪ F) := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_union, Set.mem_iUnion]
      tauto
    rw [heq] at hres
    exact hres.isConnected.isPreconnected
  · have hempty : C \ ⋃ i, γ i '' Set.Icc (0:ℝ) 1 = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hne
    have hsub : C ⊆ ⋃ i, γ i '' Set.Icc (0:ℝ) 1 := by
      rw [← Set.diff_eq_empty]
      exact hempty
    have hempty' : C \ ((⋃ i, γ i '' Set.Icc (0:ℝ) 1) ∪ F) = ∅ := by
      rw [Set.diff_eq_empty]
      exact hsub.trans Set.subset_union_left
    rw [hempty']
    exact isPreconnected_empty

end Work.Noncompact.Routing
