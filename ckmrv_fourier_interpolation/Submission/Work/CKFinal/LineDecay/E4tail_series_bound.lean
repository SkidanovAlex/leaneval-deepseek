import Mathlib
import Submission.Work.CKFinal.LineDecay.E4tail_cnb

namespace Work.CKFinal.LineDecay

theorem E4tail_series_bound (r : ℝ) (hr0 : 0 ≤ r) (hr : r ≤ 1 / 4) :
    Summable (fun n : ℕ => (((n : ℝ) + 2) ^ 4 * r ^ (n + 2))) ∧
      ∑' n : ℕ, (((n : ℝ) + 2) ^ 4 * r ^ (n + 2)) ≤ 144 * r ^ 2 := by
  have hq_lt : ‖(64 / 81 : ℝ)‖ < 1 := by norm_num
  have hq_sum : Summable (fun n : ℕ => (64 / 81 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one hq_lt
  have hq_tsum : ∑' n : ℕ, (64 / 81 : ℝ) ^ n = (1 - 64 / 81)⁻¹ :=
    tsum_geometric_of_norm_lt_one hq_lt
  have hdom : ∀ n : ℕ,
      (((n : ℝ) + 2) ^ 4 * r ^ (n + 2)) ≤ (26 * r ^ 2) * (64 / 81 : ℝ) ^ n := by
    intro n
    have hrpow : r ^ (n + 2) ≤ r ^ 2 * (1 / 4 : ℝ) ^ n := by
      rw [pow_add]
      have h1 : r ^ n ≤ (1 / 4 : ℝ) ^ n := pow_le_pow_left₀ hr0 hr n
      have h2 : (0 : ℝ) ≤ r ^ 2 := by positivity
      nlinarith [h1, h2]
    have hc := E4tail_cnb n
    have hr2 : (0 : ℝ) ≤ r ^ 2 := by positivity
    have hn4 : (0 : ℝ) ≤ ((n : ℝ) + 2) ^ 4 := by positivity
    calc (((n : ℝ) + 2) ^ 4 * r ^ (n + 2))
        ≤ ((n : ℝ) + 2) ^ 4 * (r ^ 2 * (1 / 4 : ℝ) ^ n) :=
          mul_le_mul_of_nonneg_left hrpow hn4
      _ = r ^ 2 * (((n : ℝ) + 2) ^ 4 * (1 / 4 : ℝ) ^ n) := by ring
      _ ≤ r ^ 2 * (26 * (64 / 81 : ℝ) ^ n) := mul_le_mul_of_nonneg_left hc hr2
      _ = (26 * r ^ 2) * (64 / 81 : ℝ) ^ n := by ring
  have hsum_a : Summable (fun n : ℕ => (((n : ℝ) + 2) ^ 4 * r ^ (n + 2))) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hdom (hq_sum.mul_left (26 * r ^ 2))
  refine ⟨hsum_a, ?_⟩
  have hf_sum : Summable (fun n : ℕ => (26 * r ^ 2) * (64 / 81 : ℝ) ^ n) :=
    hq_sum.mul_left _
  calc ∑' n : ℕ, (((n : ℝ) + 2) ^ 4 * r ^ (n + 2))
      ≤ ∑' n : ℕ, (26 * r ^ 2) * (64 / 81 : ℝ) ^ n :=
        hsum_a.tsum_le_tsum hdom hf_sum
    _ = (26 * r ^ 2) * ∑' n : ℕ, (64 / 81 : ℝ) ^ n := by rw [tsum_mul_left]
    _ = (26 * r ^ 2) * (1 - 64 / 81)⁻¹ := by rw [hq_tsum]
    _ ≤ 144 * r ^ 2 := by
        rw [show (1 - (64 / 81 : ℝ))⁻¹ = 81 / 17 by norm_num]
        nlinarith [sq_nonneg r]

end Work.CKFinal.LineDecay
