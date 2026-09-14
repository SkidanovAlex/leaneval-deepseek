import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.Order.Filter.AtTopBot.Basic

namespace Commons.Data.Nat

theorem eventually_heightCap_le_pow (n : ℕ) (hn : 1 ≤ n) :
    ∀ᶠ H : ℕ in Filter.atTop,
      (2 * n - 1).factorial * (n * (H + 1)) ^ (2 * n - 1) ≤ H ^ (4 * n ^ 2) := by
  rw [Filter.eventually_atTop]
  refine ⟨max 1 ((2 * n - 1).factorial * (2 * n) ^ (2 * n - 1)), fun H hH => ?_⟩
  have hH1 : 1 ≤ H := le_trans (le_max_left _ _) hH
  have hHD : (2 * n - 1).factorial * (2 * n) ^ (2 * n - 1) ≤ H :=
    le_trans (le_max_right _ _) hH
  have hstep : n * (H + 1) ≤ n * (2 * H) := by
    apply Nat.mul_le_mul_left
    omega
  have h2 : (2 * n - 1).factorial * (n * (H + 1)) ^ (2 * n - 1)
      ≤ (2 * n - 1).factorial * (n * (2 * H)) ^ (2 * n - 1) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hstep _)
  have h3 : (2 * n - 1).factorial * (n * (2 * H)) ^ (2 * n - 1)
      = ((2 * n - 1).factorial * (2 * n) ^ (2 * n - 1)) * H ^ (2 * n - 1) := by
    rw [show n * (2 * H) = (2 * n) * H by ring, mul_pow]
    ring
  have h4 : ((2 * n - 1).factorial * (2 * n) ^ (2 * n - 1)) * H ^ (2 * n - 1)
      ≤ H * H ^ (2 * n - 1) :=
    Nat.mul_le_mul_right _ hHD
  have h5 : H * H ^ (2 * n - 1) = H ^ (2 * n) := by
    rw [← pow_succ']
    congr 1
    omega
  have h6 : H ^ (2 * n) ≤ H ^ (4 * n ^ 2) := by
    apply Nat.pow_le_pow_right hH1
    nlinarith [hn]
  calc (2 * n - 1).factorial * (n * (H + 1)) ^ (2 * n - 1)
      ≤ (2 * n - 1).factorial * (n * (2 * H)) ^ (2 * n - 1) := h2
    _ = ((2 * n - 1).factorial * (2 * n) ^ (2 * n - 1)) * H ^ (2 * n - 1) := h3
    _ ≤ H * H ^ (2 * n - 1) := h4
    _ = H ^ (2 * n) := h5
    _ ≤ H ^ (4 * n ^ 2) := h6

end Commons.Data.Nat