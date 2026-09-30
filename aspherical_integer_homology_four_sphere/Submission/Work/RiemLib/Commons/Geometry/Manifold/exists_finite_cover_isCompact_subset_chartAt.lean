import Mathlib.Geometry.Manifold.IsManifold.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set

set_option linter.unusedVariables false

namespace Commons.Geometry.Manifold

/-- On a compact, locally compact charted space, `M` can be covered by finitely many compact sets,
each of which is contained in the source of the chart at some point. -/
theorem exists_finite_cover_isCompact_subset_chartAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [CompactSpace M]
    [LocallyCompactSpace M] :
    ∃ n : ℕ, ∃ z : Fin n → M, ∃ Z : Fin n → Set M,
      (∀ i, IsCompact (Z i)) ∧ (∀ i, Z i ⊆ (chartAt H (z i)).source) ∧
        (Set.univ ⊆ ⋃ i, Z i) := by
  -- Around each point, a compact set contained in the source of its chart, with the point in
  -- its interior.
  choose K hK using fun x : M =>
    exists_compact_subset (x := x) (chartAt H x).open_source (mem_chart_source H x)
  -- The interiors cover `M`; extract a finite subcover.
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : M => interior (K x))
    (fun _ => isOpen_interior) (fun x _ => mem_iUnion.mpr ⟨x, (hK x).2.1⟩)
  -- Reindex the finite cover by `Fin t.card`.
  let e : Fin t.card ≃ t :=
    (Equiv.cast (congrArg Fin (Fintype.card_coe t).symm)).trans (Fintype.equivFin t).symm
  refine ⟨t.card, fun i => (e i : M), fun i => K (e i), ?_, ?_, ?_⟩
  · intro i; exact (hK (e i)).1
  · intro i; exact (hK (e i)).2.2
  · intro m hm
    obtain ⟨x, hxt, hmx⟩ := mem_iUnion₂.mp (ht (mem_univ m))
    refine mem_iUnion.mpr ⟨e.symm ⟨x, hxt⟩, ?_⟩
    show m ∈ K (e (e.symm ⟨x, hxt⟩))
    rw [Equiv.apply_symm_apply]
    exact interior_subset hmx

end Commons.Geometry.Manifold