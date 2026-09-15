import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Analysis.Asymptotics

/-- Closed form of the finite weighted geometric sum:
`(Σ_{k=0}^{K} k·r^k) · (1−r)² = r − (K+1)·r^(K+1) + K·r^(K+2)`. -/
lemma geom_sum_range_mul_closed (r : ℝ) (K : ℕ) :
    ((∑ k ∈ Finset.range (K + 1), (k : ℝ) * r ^ k)) * (1 - r) ^ 2 =
      r - ((K + 1 : ℕ) : ℝ) * r ^ (K + 1) + (K : ℕ) * r ^ (K + 2) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
      rw [Finset.sum_range_succ]
      rw [add_mul]
      rw [ih]
      rw [pow_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      ring_nf

/-- For a ratio `0 ≤ r < 1`, every finite initial segment of the weighted
geometric series `Σ k·r^k` is at most the full value `r / (1 − r)²`. -/
theorem sum_range_mul_geom_le (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1), (k : ℝ) * r ^ k) ≤ r / (1 - r) ^ 2 := by
  have h1mr : 0 < 1 - r := by linarith
  have hden : 0 < (1 - r) ^ 2 := sq_pos_of_pos h1mr
  rw [le_div_iff₀ hden]
  rw [geom_sum_range_mul_closed r K]
  have hterm : (K : ℝ) * r ^ (K + 2) ≤ ((K + 1 : ℕ) : ℝ) * r ^ (K + 1) := by
    have hrp : 0 ≤ r ^ (K + 1) := pow_nonneg hr0 (K + 1)
    have hK0 : 0 ≤ (K : ℝ) := by exact_mod_cast Nat.zero_le K
    have hmain : (K : ℝ) * r ≤ (K : ℝ) + 1 := by
      have h1 : (K : ℝ) * r ≤ (K : ℝ) * 1 := mul_le_mul_of_nonneg_left (le_of_lt hr1) hK0
      nlinarith
    calc
      (K : ℝ) * r ^ (K + 2) = (K : ℝ) * r * r ^ (K + 1) := by
        rw [pow_succ]
        ring
      _ ≤ ((K + 1 : ℕ) : ℝ) * r ^ (K + 1) := by
        have h2 : (K : ℝ) * r ≤ ((K + 1 : ℕ) : ℝ) := by
          norm_num at hmain ⊢
          exact hmain
        exact mul_le_mul_of_nonneg_right h2 hrp
  nlinarith

end Commons.Analysis.Asymptotics