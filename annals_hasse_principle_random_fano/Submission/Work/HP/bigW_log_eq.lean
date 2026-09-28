import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP

/-- The logarithm of the product `W = ∏_{p ≤ w} p^{r_p(w)}` is the sum of the
logarithms of its prime-power factors. -/
theorem bigW_log_eq (w : ℝ) :
    Real.log ((Work.HP.bigW w : ℕ) : ℝ) =
      ∑ p ∈ Nat.primesLE ⌊w⌋₊, (Work.HP.rOf p w : ℝ) * Real.log (p : ℝ) := by
  rw [bigW, ← Nat.primesLE_eq_filter_range, Nat.cast_prod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    rw [Nat.cast_pow]
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Nat.prime_of_mem_primesLE hp)))

end Work.HP
