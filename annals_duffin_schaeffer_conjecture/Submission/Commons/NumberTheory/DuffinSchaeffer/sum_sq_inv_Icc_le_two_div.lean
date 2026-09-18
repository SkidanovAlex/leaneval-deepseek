import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries

namespace Commons.NumberTheory.DuffinSchaeffer

/-- For `1 ≤ a ≤ b`, the partial sum `∑_{n=a}^{b} 1/n²` is at most `2/a`. -/
theorem sum_sq_inv_Icc_le_two_div (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (Finset.sum (Finset.Icc a b) (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2))) ≤ (2 : ℝ) / (a : ℝ) := by
  simp_rw [one_div, div_eq_mul_inv]
  calc
    Finset.sum (Finset.Icc a b) (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹)
        = ((a : ℝ) ^ 2)⁻¹ + Finset.sum (Finset.Ioc a b) (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
          rw [Finset.Icc_eq_cons_Ioc hab]
          simp
    _ ≤ ((a : ℝ) ^ 2)⁻¹ + ((a : ℝ)⁻¹ - (b : ℝ)⁻¹) := by
          have hIoc : Finset.sum (Finset.Ioc a b) (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹)
              ≤ (a : ℝ)⁻¹ - (b : ℝ)⁻¹ := by
            exact sum_Ioc_inv_sq_le_sub (α := ℝ) (k := a) (n := b) (by omega : a ≠ 0) hab
          exact add_le_add_right hIoc _
    _ ≤ ((a : ℝ) ^ 2)⁻¹ + (a : ℝ)⁻¹ := by
          have hb0 : 0 ≤ (b : ℝ)⁻¹ := by
            exact inv_nonneg.mpr (by exact_mod_cast (Nat.zero_le b))
          linarith
    _ ≤ 2 * (a : ℝ)⁻¹ := by
          have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
          have haR0 : 0 < (a : ℝ) := lt_of_lt_of_le (by norm_num) ha1
          have hsqpos : 0 < ((a : ℝ) ^ 2) := sq_pos_of_pos haR0
          have hpow : (a : ℝ) ≤ (a : ℝ) ^ 2 := by
            nlinarith [mul_le_mul (le_of_lt haR0) ha1 (by norm_num : (0 : ℝ) ≤ 1) (le_of_lt haR0)]
          have h₁ : ((a : ℝ) ^ 2)⁻¹ ≤ (a : ℝ)⁻¹ := (inv_le_inv₀ hsqpos haR0).mpr hpow
          linarith

end Commons.NumberTheory.DuffinSchaeffer