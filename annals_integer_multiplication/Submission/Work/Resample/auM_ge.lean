import Mathlib
import Submission.Work.Resample.auTailDefs

namespace Work.Resample

/-- `√p ≤ ⌊√p⌋ + 1`, the only arithmetic input: `⌊√p⌋` is the integer square root
of `p`, so `p < (⌊√p⌋+1)²` and hence `√p < ⌊√p⌋+1`. -/
theorem sqrt_le_natSqrt_add_one (p : ℕ) :
    Real.sqrt (p : ℝ) ≤ (Nat.sqrt p : ℝ) + 1 := by
  have h := Nat.lt_succ_sqrt p
  have h' : (p : ℝ) < ((Nat.sqrt p : ℝ) + 1) ^ 2 := by
    have hs : (((Nat.sqrt p).succ : ℕ) : ℝ) = (Nat.sqrt p : ℝ) + 1 := by push_cast; ring
    calc (p : ℝ) < (((Nat.sqrt p).succ : ℕ) : ℝ) * (((Nat.sqrt p).succ : ℕ) : ℝ) := by
          exact_mod_cast h
      _ = ((Nat.sqrt p : ℝ) + 1) ^ 2 := by rw [hs]; ring
  rw [Real.sqrt_le_left (by positivity)]
  exact le_of_lt h'

/-- The window half-width `auM p α = (⌊√p⌋+1)α` dominates `α√p`. -/
theorem auM_ge (p α : ℕ) : (α : ℝ) * Real.sqrt p ≤ (auM p α : ℝ) := by
  have hp := sqrt_le_natSqrt_add_one p
  rw [auM]
  push_cast
  calc (α : ℝ) * Real.sqrt (p : ℝ) ≤ (α : ℝ) * ((Nat.sqrt p : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg α)
    _ = ((Nat.sqrt p : ℝ) + 1) * (α : ℝ) := by ring

end Work.Resample
