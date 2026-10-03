import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Sqrt

namespace Commons.Analysis.Sum

/-- Key one-step estimate: for a real number `x ≥ 1`, the reciprocal square root of `x`
is bounded by the increment of `2√·`, i.e. `(√x)⁻¹ ≤ 2(√x - √(x-1))`.
Equivalently `∫_{x-1}^{x} t^{-1/2} dt ≥ x^{-1/2}`, the usual convexity comparison
which telescopes into the bound `∑_{d ≤ D} d^{-1/2} ≤ 2√D`. -/
lemma inv_sqrt_le_two_mul_sqrt_sub (x : ℝ) (hx : 1 ≤ x) :
    (Real.sqrt x)⁻¹ ≤ 2 * (Real.sqrt x - Real.sqrt (x - 1)) := by
  have hx0 : 0 < x := by linarith
  have hxn : 0 ≤ x := le_of_lt hx0
  have ha : 0 < Real.sqrt x := Real.sqrt_pos_of_pos hx0
  have hsqx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hxn
  have hprod : Real.sqrt x * Real.sqrt (x - 1) = Real.sqrt (x * (x - 1)) :=
    (Real.sqrt_mul hxn (x - 1)).symm
  have hle : Real.sqrt (x * (x - 1)) ≤ x - 1 / 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩
  have h1 : 1 ≤ Real.sqrt x * (2 * (Real.sqrt x - Real.sqrt (x - 1))) := by
    nlinarith [hsqx, hprod, hle]
  exact (mul_le_mul_iff_right₀ ha).mp (by
    rw [mul_inv_cancel₀ (ne_of_gt ha)]
    exact h1)

theorem sum_inv_sqrt_le (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, (Real.sqrt (d : ℝ))⁻¹) ≤ 2 * Real.sqrt D := by
  induction D with
  | zero =>
      rw [Finset.Icc_eq_empty (by norm_num : ¬ (1 : ℕ) ≤ 0)]
      simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      have hpt : (Real.sqrt ((n + 1 : ℕ) : ℝ))⁻¹
          ≤ 2 * (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) := by
        have h := inv_sqrt_le_two_mul_sqrt_sub ((n + 1 : ℕ) : ℝ)
          (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
        simpa using h
      linarith

end Commons.Analysis.Sum