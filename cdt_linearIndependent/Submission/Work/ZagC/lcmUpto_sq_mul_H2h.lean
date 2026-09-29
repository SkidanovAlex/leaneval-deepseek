import Mathlib
import Submission.Work.ZagC.defs

namespace Work.ZagC

/-- `lcm(1,…,m)² · H2_k ∈ ℤ` for `k ≤ m`: every `j ≤ k` divides `lcmUpto m`, so
`lcmUpto m² · H2_k = Σ_{j ≤ k} (lcmUpto m / j)²` is a sum of squares of natural numbers. -/
theorem lcmUpto_sq_mul_H2h (m k : ℕ) (h : k ≤ m) : ∃ z : ℤ, (Submission.CDTPlan.lcmUpto m : ℚ) ^ 2 * Work.ZagC.H2h k = z := by
  refine ⟨(∑ j ∈ Finset.Icc 1 k, (Submission.CDTPlan.lcmUpto m / j) ^ 2 : ℕ), ?_⟩
  have key : (Submission.CDTPlan.lcmUpto m : ℚ) ^ 2 * Work.ZagC.H2h k
      = ((∑ j ∈ Finset.Icc 1 k, (Submission.CDTPlan.lcmUpto m / j) ^ 2 : ℕ) : ℚ) := by
    rw [Work.ZagC.H2h, Finset.mul_sum, Nat.cast_sum]
    simp only [Nat.cast_pow]
    refine Finset.sum_congr rfl ?_
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hdiv : j ∣ Submission.CDTPlan.lcmUpto m :=
      Finset.dvd_lcm (f := id) (by simp [hj.1, le_trans hj.2 h])
    obtain ⟨c, hc⟩ := hdiv
    have hj0 : 0 < j := by omega
    rw [hc, Nat.mul_div_cancel_left _ hj0]
    push_cast
    field_simp
  rw [key, Int.cast_natCast]

end Work.ZagC
