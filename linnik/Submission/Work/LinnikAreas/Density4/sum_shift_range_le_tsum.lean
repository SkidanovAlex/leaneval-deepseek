import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic

namespace Work.LinnikAreas.Density4

/-- For a nonnegative summable real sequence, the partial sum over the shifted
block `{1, …, N}` is at most the total sum. -/
theorem sum_shift_range_le_tsum (g : ℕ → ℝ) (hg : Summable g) (h0 : ∀ n, 0 ≤ g n) (N : ℕ) :
    (∑ k ∈ Finset.range N, g (k + 1)) ≤ ∑' n : ℕ, g n := by
  -- `∑_{k=0}^{N} g k = ∑_{k=0}^{N-1} g (k+1) + g 0`
  have key : (∑ k ∈ Finset.range (N + 1), g k) = (∑ k ∈ Finset.range N, g (k + 1)) + g 0 :=
    Finset.sum_range_succ' g N
  -- the full partial sum up to `N` is at most the total sum
  have hle : (∑ k ∈ Finset.range (N + 1), g k) ≤ ∑' n : ℕ, g n :=
    Summable.sum_le_tsum _ (fun i _ => h0 i) hg
  have h0' : 0 ≤ g 0 := h0 0
  linarith

end Work.LinnikAreas.Density4
