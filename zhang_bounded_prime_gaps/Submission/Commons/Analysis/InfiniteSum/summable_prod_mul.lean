import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace Commons.Analysis.InfiniteSum

theorem summable_prod_mul {ι κ : Type*} {a : ι → ℝ} {b : κ → ℝ}
    (ha : Summable a) (hb : Summable b) (hna : ∀ i, 0 ≤ a i) (hnb : ∀ j, 0 ≤ b j) :
    Summable (fun p : ι × κ => a p.1 * b p.2) := by
  refine (summable_prod_of_nonneg (fun p => mul_nonneg (hna p.1) (hnb p.2))).2 ⟨?_, ?_⟩
  · intro i
    exact hb.mul_left (a i)
  · have h : (fun i => ∑' j, a i * b j) = (fun i => a i * ∑' j, b j) := by
      funext i
      exact tsum_mul_left
    rw [h]
    exact ha.mul_right (∑' j, b j)

end Commons.Analysis.InfiniteSum