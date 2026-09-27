import Mathlib
import Submission.Work.Projection.exists_good_direction

namespace Work.Projection

open scoped Manifold ContDiff
open Topology MeasureTheory

/-- `Work.Projection.exists_good_direction`, with the extra conclusion that the direction `u` is
nonzero.  Proof: replace the bad set in the proof of `exists_good_direction` by
`badImmCharts ∪ badInjCharts ∪ {0}`, which has Hausdorff dimension `≤ 2n < k` (use
`MeasureTheory.dimH_union` and the fact that a singleton has dimension `0`), so a direction outside
it exists.  Then apply `injective_projVec_comp` and `injective_projVec_comp_mfderiv` exactly as
there. -/
theorem exists_good_direction_ne_zero {n k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hk : 2 * n + 1 ≤ k) (f : M → EuclideanSpace ℝ (Fin (k+1)))
    (hf : ContMDiff (𝓡 n) (𝓡 (k+1)) ∞ f)
    (hinj : Function.Injective f)
    (himm : ∀ x, Function.Injective (mfderiv (𝓡 n) (𝓡 (k+1)) f x))
    (p : ℕ → M)
    (hcov : (Set.univ : Set M) ⊆ ⋃ i, (chartAt (EuclideanSpace ℝ (Fin n)) (p i)).source) :
    ∃ u : EuclideanSpace ℝ (Fin k),
      u ≠ 0 ∧ Function.Injective (fun x => Work.Projection.projVec u (f x)) ∧
      ∀ x, Function.Injective (Work.Projection.projVec u ∘L mfderiv (𝓡 n) (𝓡 (k+1)) f x) := by
  set bad := (badImmCharts (n := n) (k := k) f p ∪ badInjCharts (n := n) (k := k) f p)
      ∪ ({0} : Set (EuclideanSpace ℝ (Fin k))) with hbad
  have hbound : dimH bad ≤ 2 * n := by
    rw [hbad, dimH_union, dimH_union]
    refine max_le (max_le (dimH_badImmCharts f hf p) (dimH_badInjCharts f hf p)) ?_
    rw [dimH_singleton]
    exact zero_le
  have hlt : dimH bad < dimH (Set.univ : Set (EuclideanSpace ℝ (Fin k))) := by
    rw [Real.dimH_univ_eq_finrank, finrank_euclideanSpace_fin]
    refine lt_of_le_of_lt hbound ?_
    have h2 : 2 * n < k := by omega
    exact_mod_cast h2
  obtain ⟨u, hu⟩ : ∃ u, u ∉ bad := by
    by_contra h
    rw [not_exists] at h
    simp only [not_not] at h
    have : bad = (Set.univ : Set (EuclideanSpace ℝ (Fin k))) := Set.eq_univ_iff_forall.2 h
    rw [this] at hlt
    exact lt_irrefl _ hlt
  simp only [hbad, Set.mem_union, Set.mem_singleton_iff, not_or] at hu
  exact ⟨u, hu.2, injective_projVec_comp f hinj hcov hu.1.2,
    injective_projVec_comp_mfderiv f hf himm hcov hu.1.1⟩

end Work.Projection
