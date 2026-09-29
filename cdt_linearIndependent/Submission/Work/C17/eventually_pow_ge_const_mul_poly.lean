import Mathlib

namespace Work.C17

open Filter Asymptotics

theorem eventually_pow_ge_const_mul_poly (u L : ℝ) (hu : 1 < u) (hL : 0 < L) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → L * ((n : ℝ) + 1) ^ 6 ≤ u ^ n := by
  have hu0 : 0 < u := by linarith
  have hb : 0 < Real.log u := Real.log_pos hu
  -- The polynomial is little-o of the exponential `u ^ n`.
  have hlittle : (fun n : ℕ => (n : ℝ) ^ 6) =o[atTop] (fun n : ℕ => u ^ n) := by
    have h := (isLittleO_pow_exp_pos_mul_atTop 6 hb).comp_tendsto
      tendsto_natCast_atTop_atTop
    refine h.congr' (EventuallyEq.rfl) ?_
    filter_upwards with n
    show Real.exp (Real.log u * (n : ℝ)) = u ^ n
    rw [mul_comm (Real.log u) (n : ℝ), Real.exp_nat_mul, Real.exp_log hu0]
  -- Hence eventually `L * (n+1)^6 ≤ u^n`.
  have hbound : ∀ᶠ n : ℕ in atTop, L * ((n : ℝ) + 1) ^ 6 ≤ u ^ n := by
    have hc : (0 : ℝ) < 1 / (64 * L) := by positivity
    have hev := (isLittleO_iff.mp hlittle) hc
    filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
    have hn' : (n : ℝ) ^ 6 ≤ (1 / (64 * L)) * u ^ n := by
      have h1 : ‖(n : ℝ) ^ 6‖ = (n : ℝ) ^ 6 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h2 : ‖u ^ n‖ = u ^ n := by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hu0.le n)]
      rw [h1, h2] at hn
      exact hn
    -- `(n+1)^6 ≤ 64 * n^6` for `n ≥ 1`.
    have hle : ((n : ℝ) + 1) ^ 6 ≤ 64 * (n : ℝ) ^ 6 := by
      have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have h2 : (n : ℝ) + 1 ≤ 2 * n := by linarith
      calc ((n : ℝ) + 1) ^ 6 ≤ (2 * (n : ℝ)) ^ 6 :=
            pow_le_pow_left₀ (by positivity) h2 6
        _ = 64 * (n : ℝ) ^ 6 := by ring
    have hL64 : (0 : ℝ) ≤ 64 * L := by positivity
    calc L * ((n : ℝ) + 1) ^ 6 ≤ L * (64 * (n : ℝ) ^ 6) := by
          nlinarith [hL.le, hle]
      _ = (64 * L) * (n : ℝ) ^ 6 := by ring
      _ ≤ (64 * L) * ((1 / (64 * L)) * u ^ n) :=
            mul_le_mul_of_nonneg_left hn' hL64
      _ = u ^ n := by
        have hne : (64 * L) ≠ 0 := by positivity
        rw [← mul_assoc, mul_one_div, div_self hne, one_mul]
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  exact ⟨N, fun n hn => hN n hn⟩

end Work.C17
