import Mathlib

namespace Work.FIArea7

/-- Double counting the divisor function: the sum of `τ(n)` over `n ≤ N` equals the sum over
`d ≤ N` of the number of multiples of `d` in `[1, N]`.  Indeed, for `1 ≤ n ≤ N` every divisor of
`n` lies in `[1, N]`, so `τ(n) = #{d ≤ N : d ∣ n}`; exchanging the two finite sums gives the
claim. -/
theorem sum_tau_eq_sum_card_multiples (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ((n.divisors.card : ℕ) : ℝ))
      = ∑ d ∈ Finset.Icc 1 N, ((((Finset.Icc 1 N).filter (fun b => d ∣ b)).card : ℕ) : ℝ) := by
  -- Step 1: write each `τ(n)` as an indicator sum over `d ∈ [1, N]`.
  have step1 : (∑ b ∈ Finset.Icc 1 N, ((b.divisors.card : ℕ) : ℝ))
      = ∑ b ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, (if d ∣ b then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mem_Icc] at hb
    obtain ⟨hb1, hbN⟩ := hb
    have hbne : b ≠ 0 := by omega
    have hbpos : 0 < b := by omega
    have hset : b.divisors = (Finset.Icc 1 N).filter (fun d => d ∣ b) := by
      ext d
      rw [Nat.mem_divisors]
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdvd, -⟩
        exact ⟨⟨Nat.succ_le_of_lt (Nat.pos_of_dvd_of_pos hdvd hbpos),
          le_trans (Nat.le_of_dvd hbpos hdvd) hbN⟩, hdvd⟩
      · rintro ⟨⟨hd1, -⟩, hdvd⟩
        exact ⟨hdvd, hbne⟩
    rw [hset, Finset.card_eq_sum_ones]
    push_cast
    rw [Finset.sum_filter]
  -- Step 2: the inner indicator sum is the number of multiples of `d` in `[1, N]`.
  have step3 : ∀ d ∈ Finset.Icc 1 N,
      (∑ b ∈ Finset.Icc 1 N, (if d ∣ b then (1 : ℝ) else 0))
        = (((Finset.Icc 1 N).filter (fun b => d ∣ b)).card : ℝ) := by
    intro d hd
    rw [← Finset.sum_filter]
    rw [Finset.card_eq_sum_ones]
    push_cast
    rfl
  rw [step1, Finset.sum_comm]
  exact Finset.sum_congr rfl step3

end Work.FIArea7
