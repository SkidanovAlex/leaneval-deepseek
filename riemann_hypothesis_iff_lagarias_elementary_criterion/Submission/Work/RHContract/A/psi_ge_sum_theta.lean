import Mathlib

namespace Work.RHContract.A

/-- The partial sum `∑_{k=1}^{K} θ(x^{1/k})` is bounded by `ψ x`.

This is the monotone/truncation half of the classical identity
`ψ x = ∑_{k ≥ 1} θ(x^{1/k})`: the full sum (truncated at `⌊log x / log 2⌋₊`) equals `ψ x`
(`Chebyshev.psi_eq_sum_theta'`), and each summand `θ(x^{1/k})` is nonnegative, so any partial
sum over `Icc 1 K` is at most the full sum. -/
theorem psi_ge_sum_theta (x : ℝ) (hx : 1 ≤ x) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, Chebyshev.theta (x ^ (1 / (k : ℝ)))) ≤ Chebyshev.psi x := by
  have hx0 : 0 ≤ x := by linarith
  -- Truncate the exact identity `ψ x = ∑_{n ∈ Icc 1 N} θ (x^{1/n})` at a large enough `N ≥ K`.
  set N := max K ⌊Real.log x / Real.log 2⌋₊ with hN
  rw [Chebyshev.psi_eq_sum_theta' hx0 (le_max_right _ _)]
  -- The partial sum is bounded by the full sum since all summands are nonnegative.
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (le_max_left _ _))
  intro k _ _
  exact Chebyshev.theta_nonneg _

end Work.RHContract.A
