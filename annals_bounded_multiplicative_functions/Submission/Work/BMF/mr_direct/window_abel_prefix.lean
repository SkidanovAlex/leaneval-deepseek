import Mathlib
import Submission.Work.BMF.mr_direct.abel_inv_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- `window_abel_prefix`: Abel summation with the weight `1/n` for a sequence whose *prefix sums*
`∑_{j ∈ Icc 1 k} a j` are bounded by `K * k` on the range `N ≤ k ≤ M`.

Writing `A k = ∑_{j ∈ Icc 1 k} a j`, the block sums over `Ioc N k` are
`A k - A N`, hence bounded by `K * k + K * N ≤ K * (M + N)`; the Abel estimate with the constant
partial-sum bound `K * (M + N)` (`abel_inv_bound`) then gives the claim. -/
theorem window_abel_prefix (a : ℕ → ℂ) (K : ℝ) (N M : ℕ)
    (hK : 0 ≤ K) (hN : 1 ≤ N) (hNM : N < M)
    (hA : ∀ k : ℕ, N ≤ k → k ≤ M → ‖∑ j ∈ Finset.Icc 1 k, a j‖ ≤ K * (k : ℝ)) :
    ‖∑ n ∈ Finset.Ioc N M, (((n : ℝ))⁻¹ : ℂ) * a n‖
      ≤ K * ((M : ℝ) + (N : ℝ)) * (1 / (M : ℝ) + 1 / ((N + 1 : ℕ) : ℝ)) := by
  -- The block sum over `Ioc N k` is the difference of the prefix sums at `k` and at `N`.
  have hsplit : ∀ k : ℕ, N ≤ k → (∑ i ∈ Finset.Ioc N k, a i)
      = (∑ i ∈ Finset.Icc 1 k, a i) - (∑ i ∈ Finset.Icc 1 N, a i) := by
    intro k hk
    have hunion : Finset.Icc 1 k = Finset.Icc 1 N ∪ Finset.Ioc N k := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      omega
    have hdisj : Disjoint (Finset.Icc 1 N) (Finset.Ioc N k) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_Icc] at hx
      simp only [Finset.mem_Ioc] at hx'
      omega
    have h := Finset.sum_union (f := a) hdisj
    rw [← hunion] at h
    rw [h]; ring
  -- Constant bound `K * (M + N)` for the partial sums over `Ioc N k`, `N < k ≤ M`.
  have hpartial : ∀ k, N < k → k ≤ M → ‖∑ j ∈ Finset.Ioc N k, a j‖ ≤ K * ((M : ℝ) + (N : ℝ)) := by
    intro k hNk hkM
    have hkN : N ≤ k := le_of_lt hNk
    have hNleM : N ≤ M := le_of_lt hNM
    rw [hsplit k hkN]
    calc ‖(∑ i ∈ Finset.Icc 1 k, a i) - (∑ i ∈ Finset.Icc 1 N, a i)‖
        ≤ ‖∑ i ∈ Finset.Icc 1 k, a i‖ + ‖∑ i ∈ Finset.Icc 1 N, a i‖ := norm_sub_le _ _
      _ ≤ K * (k : ℝ) + K * (N : ℝ) := add_le_add (hA k hkN hkM) (hA N le_rfl hNleM)
      _ ≤ K * (M : ℝ) + K * (N : ℝ) := by
            have hkM' : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast hkM
            have := mul_le_mul_of_nonneg_left hkM' hK
            linarith
      _ = K * ((M : ℝ) + (N : ℝ)) := by ring
  exact abel_inv_bound a (K * ((M : ℝ) + (N : ℝ))) N M hNM hpartial

end Work.BMF.mr_direct
