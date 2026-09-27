import Mathlib
import Submission.Work.EKLC8Core.Vol

/-!
# Step 10 (D3): the second choice `r` always gives drift `≥ ρ²`

This file proves `Work.EKLC8Core.step10_second_choice`, the second of the two
alternatives in Step 10 of the low-entropy argument (`ROUTE_LEAD.md` §5).

`kappa G = max(κ_a, κ_u)` is by definition a `max`, so it dominates both the diagonal
anisotropy `κ_a = |g₁₁ - g₀₀|` and the bare root-coordinate `|g₀₁| = (√|g₀₁|)²`.  The
hypothesis `ρ²κ² ≤ |g₀₁|` therefore says that the `(0,1)` entry of `G` is large at scale
`ρ²κ²`, while `|g₁₁ - g₀₀| ≤ κ`.  For `|r|` in the window
`(ρ⁻¹)⁴κ⁻¹ < |r| ≤ (ρ⁻¹)⁵κ⁻¹` the quadratic term `g₀₁r²` has size at least
`(ρ⁻¹)⁶ ≫ (ρ⁻¹)⁵ ≥ ρ²`, whereas the linear term `(g₁₁-g₀₀)r` has size at most
`(ρ⁻¹)⁵`.  Since `drift G r` dominates the combination `(g₁₁-g₀₀)r - g₀₁r²`, the
reverse triangle inequality gives `drift G r > (ρ⁻¹)⁶ - (ρ⁻¹)⁵ ≥ ρ²`.
-/

namespace Work.EKLC8Core

/-- `κ_a(g) ≤ κ(g)`: the diagonal anisotropy is the first of the two terms of `kappa`. -/
theorem kappaA_le_kappa (G : Matrix (Fin 3) (Fin 3) ℝ) : kappaA G ≤ kappa G :=
  le_max_left _ _

/-- `κ_u(g) ≤ κ(g)`: the root-coordinate term is the second of the two terms of `kappa`. -/
theorem kappaU_le_kappa (G : Matrix (Fin 3) (Fin 3) ℝ) : kappaU G ≤ kappa G :=
  le_max_right _ _

/-- `√|g₀₁| ≤ κ(g)`, i.e. the `(0,1)` root coordinate is one of the terms of `κ_u ≤ κ`. -/
theorem sqrt_abs_G10_le_kappa (G : Matrix (Fin 3) (Fin 3) ℝ) :
    Real.sqrt |G 1 0| ≤ kappa G :=
  le_trans (le_max_left _ _) (kappaU_le_kappa G)

/-- `|g₀₁| ≤ κ(g)²`: the "large `(0,1)` entry" alternative of the Step 10 dichotomy is
literally a square of `κ`. -/
theorem abs_G10_le_kappa_sq (G : Matrix (Fin 3) (Fin 3) ℝ) : |G 1 0| ≤ kappa G ^ 2 := by
  calc |G 1 0| = (Real.sqrt |G 1 0|) ^ 2 := (Real.sq_sqrt (abs_nonneg _)).symm
    _ ≤ kappa G ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_abs_G10_le_kappa G) 2

/-- **Step 10, second choice (D3).**  If the `(0,1)` entry of `G` is large at scale
`ρ²κ²` (the second alternative of the dichotomy of Step 10) and `r` lies in the window
`(ρ⁻¹)⁴κ⁻¹ < |r| ≤ (ρ⁻¹)⁵κ⁻¹`, then the drift is at least `ρ²`. -/
theorem step10_second_choice {ρ κ r : ℝ} {G : Matrix (Fin 3) (Fin 3) ℝ}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (hκ : 0 < κ) (hκκ : kappa G = κ)
    (hbad : ρ ^ 2 * κ ^ 2 ≤ |G 1 0|)
    (hr1 : (ρ⁻¹) ^ 4 * κ⁻¹ < |r|) (hr2 : |r| ≤ (ρ⁻¹) ^ 5 * κ⁻¹) :
    ρ ^ 2 ≤ drift G r := by
  -- `κ` dominates the diagonal anisotropy and the `(0,1)` entry (as a square).
  have hA : |G 1 1 - G 0 0| ≤ κ := by
    rw [← hκκ]
    exact kappaA_le_kappa G
  have hρpos : 0 < ρ⁻¹ := inv_pos.mpr hρ0
  have hκpos : 0 < κ⁻¹ := inv_pos.mpr hκ
  have hcpos : 0 < (ρ⁻¹) ^ 4 * κ⁻¹ := by positivity
  -- The quadratic term `g₀₁r²` is larger than `(ρ⁻¹)⁶`.
  have hr_sq : ((ρ⁻¹) ^ 4 * κ⁻¹) ^ 2 < r ^ 2 := by
    have h := mul_self_lt_mul_self hcpos.le hr1
    simpa [pow_two, abs_mul_abs_self] using h
  have hG10pos : 0 < |G 1 0| := by
    have : 0 < ρ ^ 2 * κ ^ 2 := by positivity
    linarith
  have hb_low : (ρ⁻¹) ^ 6 < |G 1 0| * r ^ 2 := by
    have h1 : (ρ⁻¹) ^ 6 = ρ ^ 2 * κ ^ 2 * ((ρ⁻¹) ^ 4 * κ⁻¹) ^ 2 := by field_simp
    have h2 : ρ ^ 2 * κ ^ 2 * ((ρ⁻¹) ^ 4 * κ⁻¹) ^ 2 ≤
        |G 1 0| * ((ρ⁻¹) ^ 4 * κ⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_right hbad (sq_nonneg _)
    have h3 : |G 1 0| * ((ρ⁻¹) ^ 4 * κ⁻¹) ^ 2 < |G 1 0| * r ^ 2 :=
      mul_lt_mul_of_pos_left hr_sq hG10pos
    linarith
  -- The linear term `(g₁₁-g₀₀)r` is at most `(ρ⁻¹)⁵`.
  have ha_up : |(G 1 1 - G 0 0) * r| ≤ (ρ⁻¹) ^ 5 := by
    rw [abs_mul]
    calc |G 1 1 - G 0 0| * |r| ≤ κ * |r| := mul_le_mul_of_nonneg_right hA (abs_nonneg r)
      _ ≤ κ * ((ρ⁻¹) ^ 5 * κ⁻¹) := mul_le_mul_of_nonneg_left hr2 hκ.le
      _ = (ρ⁻¹) ^ 5 := by field_simp
  -- Numerical comparison: `ρ² ≤ (ρ⁻¹)⁶ - (ρ⁻¹)⁵`.
  have hinv2 : (2:ℝ) ≤ ρ⁻¹ := by
    have h := (inv_le_inv₀ (show (0:ℝ) < 1/2 by norm_num) hρ0).mpr hρ1
    norm_num at h; exact h
  have hinv5 : ((1:ℝ) / 4) ≤ (ρ⁻¹) ^ 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hinv2 5
    rw [show (2:ℝ) ^ 5 = 32 by norm_num] at h
    linarith
  have hρ2 : ρ ^ 2 ≤ 1/4 := by
    have h := pow_le_pow_left₀ hρ0.le hρ1 2
    norm_num at h; exact h
  have hfinal : ρ ^ 2 ≤ (ρ⁻¹) ^ 6 - (ρ⁻¹) ^ 5 := by
    have h1 : (1:ℝ) ≤ ρ⁻¹ - 1 := by linarith
    have h2 : (ρ⁻¹) ^ 5 ≤ (ρ⁻¹) ^ 6 - (ρ⁻¹) ^ 5 := by
      have hrw : (ρ⁻¹) ^ 6 - (ρ⁻¹) ^ 5 = (ρ⁻¹) ^ 5 * (ρ⁻¹ - 1) := by ring
      rw [hrw]
      calc (ρ⁻¹) ^ 5 = (ρ⁻¹) ^ 5 * 1 := by ring
        _ ≤ (ρ⁻¹) ^ 5 * (ρ⁻¹ - 1) :=
            mul_le_mul_of_nonneg_left h1 (pow_nonneg hρpos.le 5)
    linarith
  -- `drift` dominates the combination `(g₁₁-g₀₀)r - g₀₁r²`.
  have hdrift : |(G 1 1 - G 0 0) * r - G 1 0 * r ^ 2| ≤ drift G r := by
    show _ ≤ max (max |(G 1 1 - G 0 0) * r - G 1 0 * r ^ 2| |G 1 2 * r|) |G 2 0 * r|
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hb_eq : |G 1 0 * r ^ 2| = |G 1 0| * r ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg r)]
  have hsplit : |G 1 0 * r ^ 2| - |(G 1 1 - G 0 0) * r| ≤
      |(G 1 1 - G 0 0) * r - G 1 0 * r ^ 2| := by
    have h := abs_sub_abs_le_abs_sub (G 1 0 * r ^ 2) ((G 1 1 - G 0 0) * r)
    rw [abs_sub_comm] at h
    linarith
  rw [← hb_eq] at hb_low
  linarith

end Work.EKLC8Core
