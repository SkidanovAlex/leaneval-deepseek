import Mathlib

namespace Work.Drive

/-- **A compact set in a charted `4`-manifold has a finite cover by compact sets each of which is
contained in the interior of a compact set lying in a chart source.** -/
theorem exists_compact_chart_cover {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (A : Set M) (hA : IsCompact A) :
    ∃ (r : ℕ) (p : Fin r → M) (C0 C1 : Fin r → Set M),
      (∀ i, IsCompact (C0 i)) ∧ (∀ i, IsCompact (C1 i)) ∧
      (∀ i, C0 i ⊆ interior (C1 i)) ∧
      (∀ i, C1 i ⊆ (chartAt (EuclideanSpace ℝ (Fin 4)) (p i)).source) ∧
      A ⊆ ⋃ i, C0 i := by
  -- A charted space over `ℝ^4` (a locally compact space) is locally compact.
  have : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 4)) M
  -- Around every point: a compact set contained in the chart source at that point, and a smaller
  -- compact set contained in the interior of the former.
  choose K1 hK1c hK1int hK1sub using fun x : M =>
    exists_compact_subset (x := x) ((chartAt (EuclideanSpace ℝ (Fin 4)) x).open_source)
      (mem_chart_source _ x)
  choose K0 hK0c hK0int hK0sub using fun x : M =>
    exists_compact_subset (x := x) (U := interior (K1 x)) isOpen_interior (hK1int x)
  -- The (open) interiors of the sets `K0 x` cover the compact set `A`; extract a finite subcover.
  have hcov : A ⊆ ⋃ x : M, interior (K0 x) := fun a ha =>
    Set.mem_iUnion.mpr ⟨a, hK0int a⟩
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun x : M => interior (K0 x))
    (fun _ => isOpen_interior) hcov
  -- Enumerate the finite subcover and use it as the required cover.
  refine ⟨t.card, fun i => (t.equivFin.symm i).1, fun i => K0 (t.equivFin.symm i).1,
    fun i => K1 (t.equivFin.symm i).1, fun i => hK0c _, fun i => hK1c _,
    fun i => hK0sub _, fun i => hK1sub _, ?_⟩
  intro a ha
  have hmem := ht ha
  rw [Set.mem_iUnion₂] at hmem
  rcases hmem with ⟨x, hxt, hax⟩
  obtain ⟨i, hi⟩ := (t.equivFin.symm).surjective ⟨x, hxt⟩
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  have hval : (t.equivFin.symm i).1 = x := by rw [hi]
  rw [hval]
  exact interior_subset hax

end Work.Drive
