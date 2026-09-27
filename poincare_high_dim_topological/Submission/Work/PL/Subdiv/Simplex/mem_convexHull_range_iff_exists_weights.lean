import Mathlib
import Submission.Work.PL.Defs

namespace Work.PL.Subdiv.Simplex

/-- A point of `E N` lies in the convex hull of the range of a finite family `v` iff it is a
convex combination of the `v i` with nonnegative weights summing to one. -/
theorem mem_convexHull_range_iff_exists_weights {N : ℕ} {ι : Type*} [Fintype ι] (v : ι → PL.E N)
    (x : PL.E N) :
    x ∈ convexHull ℝ (Set.range v) ↔
      ∃ t : ι → ℝ, (∀ i, 0 ≤ t i) ∧ ∑ i, t i = 1 ∧ ∑ i, t i • v i = x := by
  classical
  constructor
  · intro hx
    rw [convexHull_range_eq_exists_affineCombination (v := v)] at hx
    obtain ⟨s, w, hw0, hw1, hxw⟩ := hx
    refine ⟨fun i => if i ∈ s then w i else 0, ?_, ?_, ?_⟩
    · intro i
      by_cases h : i ∈ s
      · simpa [h] using hw0 i h
      · simp [h]
    · rw [Finset.sum_ite_mem_eq]; exact hw1
    · have hsum : (∑ i, (if i ∈ s then w i else 0) • v i) = ∑ i ∈ s, w i • v i := by
        simp only [ite_smul, zero_smul]
        exact Finset.sum_ite_mem_eq s (fun i => w i • v i)
      rw [hsum, ← Finset.affineCombination_eq_linear_combination s v w hw1, hxw]
  · rintro ⟨t, ht0, ht1, ht⟩
    exact mem_convexHull_of_exists_fintype t v ht0 ht1 (fun i => Set.mem_range_self i) ht

end Work.PL.Subdiv.Simplex
