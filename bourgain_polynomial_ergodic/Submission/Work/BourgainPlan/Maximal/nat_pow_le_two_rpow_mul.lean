import Mathlib

namespace Work.BourgainPlan.Maximal

/-- Polynomial growth is beaten by exponential growth: for every natural `L` and every `b > 0`
there is `N₀` such that `n ^ L ≤ 2 ^ (b * n)` for all `n ≥ N₀`. -/
theorem nat_pow_le_two_rpow_mul (L : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (n : ℝ) ^ L ≤ (2 : ℝ) ^ (b * (n : ℝ)) := by
  have h2b : 1 < (2 : ℝ) ^ b := Real.one_lt_rpow (by norm_num) hb
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) L h2b).def one_pos :
      ∀ᶠ n : ℕ in Filter.atTop, ‖(n : ℝ) ^ L‖ ≤ 1 * ‖((2 : ℝ) ^ b) ^ n‖)
  refine ⟨N, fun n hn => ?_⟩
  have hn' := hN n hn
  rw [one_mul, Real.norm_of_nonneg (pow_nonneg (Nat.cast_nonneg n) L),
      Real.norm_of_nonneg (pow_nonneg (Real.rpow_nonneg (by norm_num) b) n)] at hn'
  rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
  exact hn'

end Work.BourgainPlan.Maximal
