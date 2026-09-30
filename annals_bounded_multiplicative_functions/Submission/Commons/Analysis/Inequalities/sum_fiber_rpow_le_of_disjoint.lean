import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Inequalities.sum_rpow_inv_le_sum_rpow_inv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Inequalities

open scoped NNReal ENNReal BigOperators

/-- If the fibers `T i` (`i ∈ s`) are pairwise disjoint and each is contained in `t`, then the
sum of the `r`-th powers (`r ≥ 1`) of the fiber sums is at most the `r`-th power of the total sum
over `t`. -/
theorem sum_fiber_rpow_le_of_disjoint {ι α : Type*} (s : Finset ι) (T : ι → Finset α)
    (t : Finset α) (hdisj : (s : Set ι).PairwiseDisjoint fun i => (T i : Set α))
    (hsub : ∀ i ∈ s, T i ⊆ t) (a : α → ENNReal) {r : ℝ} (hr : 1 ≤ r) :
    ∑ i ∈ s, (∑ j ∈ T i, a j) ^ r ≤ (∑ j ∈ t, a j) ^ r := by
  classical
  -- Convert the set-disjointness of the fibers into `Finset`-disjointness.
  have hdisj' : (s : Set ι).PairwiseDisjoint T := Finset.pairwiseDisjoint_coe.mp hdisj
  -- The union of the disjoint fibers lies in `t`.
  have hsub' : s.biUnion T ⊆ t := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, hi, hxi⟩ := hx
    exact hsub i hi hxi
  -- The total mass over the disjoint fibers is at most the total mass over `t`.
  have hsum_le : ∑ i ∈ s, ∑ j ∈ T i, a j ≤ ∑ j ∈ t, a j := by
    rw [← Finset.sum_biUnion (f := a) hdisj']
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub' (fun x _ _ => zero_le)
  calc ∑ i ∈ s, (∑ j ∈ T i, a j) ^ r
      ≤ (∑ i ∈ s, ∑ j ∈ T i, a j) ^ r :=
        finset_sum_rpow_le_of_one_le s (fun i => ∑ j ∈ T i, a j) hr
    _ ≤ (∑ j ∈ t, a j) ^ r := ENNReal.rpow_le_rpow hsum_le (by linarith)

end Commons.Analysis.Inequalities