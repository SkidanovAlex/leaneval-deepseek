import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Real

theorem le_rpow_of_pow_mul_le {x c C : ℝ} {n : ℕ} (hc : 0 < c) (hn : 0 < n) (hx : 0 < x) (h : x ^ n * c ≤ C) : x ≤ (C / c) ^ (1 / (n : ℝ)) := by
  have hxpow_pos : 0 < x ^ n := pow_pos hx n
  have hn' : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  have hnc : x ^ n ≤ C / c := (le_div_iff₀ hc).mpr h
  have hnn : 0 ≤ ((n : ℝ))⁻¹ := by positivity
  calc x = (x ^ n) ^ ((n : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hx.le hn').symm
    _ ≤ (C / c) ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow hxpow_pos.le hnc hnn
    _ = (C / c) ^ (1 / (n : ℝ)) := by rw [one_div]

end Commons.Analysis.Real