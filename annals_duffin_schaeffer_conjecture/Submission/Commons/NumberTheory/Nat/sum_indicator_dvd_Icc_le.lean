import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Real.Basic

namespace Commons.NumberTheory.Nat

theorem sum_indicator_dvd_Icc_le (m q : ℕ) :
    (∑ h ∈ Finset.Icc 1 m, (if q ∣ h then (1 : ℝ) else 0)) ≤ (m : ℝ) / (q : ℝ) := by
  rw [Finset.sum_boole]
  have hcard : {x ∈ Finset.Icc 1 m | q ∣ x}.card = m / q := by
    rw [← Nat.Ioc_filter_dvd_card_eq_div m q]
    congr 1
  rw [hcard]
  exact Nat.cast_div_le (α := ℝ)

end Commons.NumberTheory.Nat