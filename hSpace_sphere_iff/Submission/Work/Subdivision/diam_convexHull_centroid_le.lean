import Mathlib
import Submission.Work.Subdivision.mesh_step

namespace Work.Subdivision

/-- The convex hull of the centroids `((F i).card : ℝ)⁻¹ • ∑ a ∈ F i, p a` of a monotone chain
of nonempty finsets has diameter at most `(card ι - 1)/card ι` times the diameter of `range p`.

Indeed the convex hull has the same diameter as the set of centroids itself
(`convexHull_diam`), and any two centroids of nested nonempty finsets are within
`(card ι - 1)/card ι * diam (range p)` by `mesh_step`. -/
theorem diam_convexHull_centroid_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (p : ι → E) {j : ℕ} (F : Fin (j+1) → Finset ι)
    (hne : ∀ i, (F i).Nonempty) (hmono : Monotone F) :
    Metric.diam (convexHull ℝ (Set.range fun i => ((F i).card : ℝ)⁻¹ • ∑ a ∈ F i, p a))
      ≤ ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι) * Metric.diam (Set.range p) := by
  classical
  -- The convex hull has the same diameter as the set of centroids.
  rw [convexHull_diam]
  -- `ι` is nonempty, since `F 0` is nonempty.
  have hneι : Nonempty ι := by
    obtain ⟨a, _⟩ := hne ⟨0, Nat.succ_pos j⟩
    exact ⟨a⟩
  have hcard_pos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr hneι
  have hcard1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcard_pos
  -- The bound is nonnegative.
  have hC : 0 ≤ ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι) * Metric.diam (Set.range p) := by
    apply mul_nonneg
    · apply div_nonneg <;> linarith
    · exact Metric.diam_nonneg
  -- Reduce the diameter bound to a pairwise bound on the centroids.
  refine Metric.diam_le_of_forall_dist_le hC ?_
  intro x hx y hy
  rcases hx with ⟨i, rfl⟩
  rcases hy with ⟨i', rfl⟩
  rw [dist_eq_norm]
  rcases le_total i i' with h | h
  · -- `F i ⊆ F i'`
    exact mesh_step p (F i) (F i') (hne i) (hmono h)
  · -- `F i' ⊆ F i`
    rw [norm_sub_rev]
    exact mesh_step p (F i') (F i) (hne i') (hmono h)

end Work.Subdivision
