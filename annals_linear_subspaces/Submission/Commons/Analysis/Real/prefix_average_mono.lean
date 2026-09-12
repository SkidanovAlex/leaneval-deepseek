import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Commons.Analysis.Real

/-- One-step monotonicity of prefix averages of a monotone sequence: adjoining one more
(no smaller) term does not decrease the average. -/
theorem prefix_average_succ_le (a : ℕ → ℝ) (ha : Monotone a) {n : ℕ} (hn : 0 < n) :
    (∑ i ∈ Finset.range n, a i) / (n : ℝ)
      ≤ (∑ i ∈ Finset.range (n + 1), a i) / ((n + 1 : ℕ) : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1R : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hle : (∑ i ∈ Finset.range n, a i) ≤ (n : ℝ) * a n := by
    calc (∑ i ∈ Finset.range n, a i) ≤ ∑ i ∈ Finset.range n, a n :=
          Finset.sum_le_sum (fun i hi => ha (le_of_lt (Finset.mem_range.mp hi)))
      _ = (n : ℝ) * a n := by
          simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [div_le_div_iff₀ hnR hn1R, hcast, Finset.sum_range_succ]
  nlinarith [hle]

/-- The prefix averages of a monotone real sequence are nondecreasing in the number of
terms. -/
theorem prefix_average_mono (a : ℕ → ℝ) (ha : Monotone a) {k l : ℕ} (hk : 0 < k) (hkl : k ≤ l) :
    (∑ i ∈ Finset.range k, a i) / (k : ℝ) ≤ (∑ i ∈ Finset.range l, a i) / (l : ℝ) := by
  refine Nat.le_induction (le_refl _) (fun n hn ih => ?_) l hkl
  exact ih.trans (prefix_average_succ_le a ha (lt_of_lt_of_le hk hn))

end Commons.Analysis.Real