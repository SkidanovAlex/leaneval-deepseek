import Mathlib.Geometry.Manifold.PartitionOfUnity

open scoped _root_.Manifold ContDiff Topology
open Bundle Set

namespace Commons.Geometry.Manifold

/-- **Smooth partition of unity on a compact set** (Urysohn-type, for a finite open cover).  On a
sigma-compact Hausdorff smooth manifold MODELLED ON A FINITE-DIMENSIONAL SPACE, for a compact set
`t` covered by finitely many open sets `s i`, there are non-negative smooth functions `f i` with
`tsupport (f i) ⊆ s i` and `sum i, f i = 1` on `t`.

The finite-dimensionality of the model space is essential (it is what provides smooth bump
functions; the statement is false for general infinite-dimensional Banach models). -/
theorem exists_contMDiff_sum_one_of_isCompact {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M] [SigmaCompactSpace M] {n : ℕ} {t : Set M} (ht : IsCompact t)
    {s : Fin n → Set M} (hs : ∀ i, IsOpen (s i)) (hst : t ⊆ ⋃ i, s i) :
    ∃ f : Fin n → M → ℝ, (∀ i, ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ (f i)) ∧
      (∀ i, tsupport (f i) ⊆ s i) ∧ (∀ i x, 0 ≤ f i x) ∧ EqOn (∑ i, f i) 1 t := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I ht.isClosed s hs hst
  refine ⟨fun i => ρ i, fun i => (ρ i).contMDiff, fun i => hρ i, fun i x => ρ.nonneg i x, ?_⟩
  intro x hx
  rw [Finset.sum_apply, ← finsum_eq_sum_of_fintype, Pi.one_apply]
  exact ρ.sum_eq_one hx

end Commons.Geometry.Manifold