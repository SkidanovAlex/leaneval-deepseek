import Mathlib
import Submission.Work.LinnikAreas.Density4.tau_divisor_sum_eq_hyperbola
import Submission.Work.LinnikAreas.Density4.rpow_neg_three_halves_sum_le_four

namespace Work.LinnikAreas.Density4

/-- The `τ`-weighted `3/2`-power sum is bounded uniformly by 16: since `τ(e) = #{ab = e}` (`Nat.divisors` / `Finset.card`), `Σ_{e ≤ N} τ(e)/e^{3/2} ≤ (Σ_{a ≤ N} a^{-3/2})²`, and the telescoping inequality `4(1/√a − 1/√(a+1)) ≥ a^{-3/2}` (equivalent to `3a−1 ≥ √(a(a+1))`, i.e. `8a²−7a+1 ≥ 0`, true for `a ≥ 1`) gives `Σ_{a ≤ N} a^{-3/2} ≤ 4(1−1/√(N+1)) ≤ 4`. -/
theorem tau_rpow_sum_bound (N : ℕ) :
    (∑ e ∈ Finset.Icc 1 N, (e.divisors.card : ℝ) / (e : ℝ) ^ (3 / 2 : ℝ)) ≤ 16 := by
  -- Rewrite the target as a sum of `τ(e)·e^{-3/2}`.
  have hconv : (∑ e ∈ Finset.Icc 1 N, (e.divisors.card : ℝ) / (e : ℝ) ^ (3 / 2 : ℝ))
      = ∑ e ∈ Finset.Icc 1 N, (e.divisors.card : ℝ) * (e : ℝ) ^ (-(3 / 2 : ℝ)) := by
    apply Finset.sum_congr rfl
    intro e he
    rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity : (0:ℝ) ≤ (e:ℝ)) (3/2)]
  rw [hconv]
  -- `S` denotes the partial sum `Σ_{a ≤ N} a^{-3/2}`.
  set S : ℝ := ∑ a ∈ Finset.Icc 1 N, (a : ℝ) ^ (-(3 / 2 : ℝ)) with hS
  have hSnonneg : 0 ≤ S := by
    rw [hS]; exact Finset.sum_nonneg (fun a ha => by positivity)
  -- Double counting: group the pairs `(a,b)`, `a·b ≤ N`, by `e = a·b`.
  rw [tau_divisor_sum_eq_hyperbola N]
  -- Factor `(a·b)^{-3/2} = a^{-3/2}·b^{-3/2}`.
  have hfac : (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a), ((a * b : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))
      = ∑ a ∈ Finset.Icc 1 N,
          (a:ℝ)^(-(3/2:ℝ)) * (∑ b ∈ Finset.Icc 1 (N / a), (b:ℝ)^(-(3/2:ℝ))) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
  rw [hfac]
  -- Each inner partial sum is at most `S` because `N / a ≤ N`.
  have hinner : ∀ a ∈ Finset.Icc 1 N, (∑ b ∈ Finset.Icc 1 (N / a), (b:ℝ)^(-(3/2:ℝ))) ≤ S := by
    intro a ha
    rw [hS]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.Icc_subset_Icc_right (Nat.div_le_self N a)
    · intro b hb hnb; positivity
  calc ∑ a ∈ Finset.Icc 1 N, (a:ℝ)^(-(3/2:ℝ)) * (∑ b ∈ Finset.Icc 1 (N / a), (b:ℝ)^(-(3/2:ℝ)))
      ≤ ∑ a ∈ Finset.Icc 1 N, (a:ℝ)^(-(3/2:ℝ)) * S := by
        apply Finset.sum_le_sum
        intro a ha
        exact mul_le_mul_of_nonneg_left (hinner a ha) (by positivity)
    _ = S * S := by rw [hS, Finset.sum_mul]
    _ ≤ 16 := by
        have hS4 : S ≤ 4 := by rw [hS]; exact rpow_neg_three_halves_sum_le_four N
        have := mul_le_mul hS4 hS4 hSnonneg (by norm_num : (0:ℝ) ≤ 4)
        linarith [this]

end Work.LinnikAreas.Density4
