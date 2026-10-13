import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

theorem rpowMajorant :
    (∀ (m : ℕ), 1 ≤ m → ∀ r : ℝ, r ≤ 3 →
        ((m : ℝ) + 1) ^ (r + 3 / 2)
          ≤ 8 * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1)) ∧
    (∀ D : ℝ, Summable fun m : ℕ => D * (((m : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) ∧
    (∀ (m : ℕ), 1 ≤ m → ∀ e : ℝ, 3 / 2 ≤ e →
        (((m : ℝ) + 1) ^ e)⁻¹ ≤ (((m : ℝ) + 1) ^ (3 / 2 : ℝ))⁻¹) := by
  refine ⟨?_, ?_, ?_⟩
  · -- The `rpow` majorant: `(m+1)^{r+3/2} ≤ 8 λ_m² √(2m+1)`.
    intro m hm r hr
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hbase : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by linarith
    -- monotonicity in the exponent, since `r + 3/2 ≤ 9/2` and the base is `≥ 1`
    have h1 : ((m : ℝ) + 1) ^ (r + 3 / 2) ≤ ((m : ℝ) + 1) ^ ((9 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
    -- `(m+1)^{9/2} = (m+1)^4 √(m+1)`
    have h2 : ((m : ℝ) + 1) ^ ((9 : ℝ) / 2) = ((m : ℝ) + 1) ^ 4 * Real.sqrt ((m : ℝ) + 1) := by
      have hh : ((9 : ℝ) / 2) = 4 + 1 / 2 := by norm_num
      rw [hh, Real.rpow_add hpos]
      rw [show ((m : ℝ) + 1) ^ (4 : ℝ) = ((m : ℝ) + 1) ^ 4 by norm_num]
      rw [← Real.sqrt_eq_rpow]
    -- the polynomial bound `(m+1)^4 ≤ 32 m² (2m+5)²`
    have h3 : ((m : ℝ) + 1) ^ 4 ≤ 32 * (m : ℝ) ^ 2 * (2 * (m : ℝ) + 5) ^ 2 := by
      nlinarith [hmR]
    have h4 : Real.sqrt ((m : ℝ) + 1) ≤ Real.sqrt (2 * (m : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    have h5 : ((m : ℝ) + 1) ^ 4 * Real.sqrt ((m : ℝ) + 1)
        ≤ 32 * (m : ℝ) ^ 2 * (2 * (m : ℝ) + 5) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) :=
      mul_le_mul h3 h4 (Real.sqrt_nonneg _) (by positivity)
    have h6 : 32 * (m : ℝ) ^ 2 * (2 * (m : ℝ) + 5) ^ 2
        = 8 * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 := by
      simp only [Work.FTS.PhiStar.Gegenbauer.lam]; ring
    calc ((m : ℝ) + 1) ^ (r + 3 / 2) ≤ ((m : ℝ) + 1) ^ ((9 : ℝ) / 2) := h1
      _ = ((m : ℝ) + 1) ^ 4 * Real.sqrt ((m : ℝ) + 1) := h2
      _ ≤ 32 * (m : ℝ) ^ 2 * (2 * (m : ℝ) + 5) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) := h5
      _ = 8 * (Work.FTS.PhiStar.Gegenbauer.lam m) ^ 2 * Real.sqrt (2 * (m : ℝ) + 1) := by rw [h6]
  · -- The comparison series `∑ (m+1)^{-3/2}` converges.
    intro D
    have h : Summable (fun n : ℕ => (((n : ℕ) : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
      Real.summable_nat_rpow_inv.mpr (by norm_num)
    have h2 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2))⁻¹) :=
      (summable_nat_add_iff (f := fun n : ℕ => (((n : ℕ) : ℝ) ^ ((3 : ℝ) / 2))⁻¹) 1).mpr h
    have h3 : Summable (fun m : ℕ => (((m : ℝ) + 1) ^ ((3 : ℝ) / 2))⁻¹) := by
      simpa [Nat.cast_add, Nat.cast_one] using h2
    exact h3.mul_left D
  · -- `(m+1)^{-e} ≤ (m+1)^{-3/2}` for `e ≥ 3/2`, base `≥ 1`.
    intro m hm e he
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hbase : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith
    have hx : (0 : ℝ) ≤ (m : ℝ) + 1 := by linarith
    rw [← Real.rpow_neg hx e, ← Real.rpow_neg hx (3 / 2)]
    exact Real.rpow_le_rpow_of_exponent_le hbase (by linarith)

end Work.FTS.PhiStar.Series.Deleg
