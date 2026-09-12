import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Commons.Analysis.Real

theorem exists_pow_log_div_sqrt_le (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : ℝ, 1 ≤ Y ∧ ∀ y : ℝ, Y ≤ y → (Real.log y) ^ n / Real.sqrt y ≤ ε := by
  have hlo : (fun x : ℝ => Real.log x ^ (n : ℝ)) =o[Filter.atTop]
      (fun x : ℝ => x ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop (n : ℝ) (by norm_num)
  have hbound := hlo.bound hε
  have hev : ∀ᶠ y : ℝ in Filter.atTop, (Real.log y) ^ n / y ^ (1 / 2 : ℝ) ≤ ε := by
    filter_upwards [hbound, Filter.eventually_ge_atTop (1 : ℝ)] with y hb hy
    have hy0 : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy
    have hlog : 0 ≤ Real.log y := Real.log_nonneg hy
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog _),
        Real.norm_of_nonneg (Real.rpow_nonneg hy0.le _), Real.rpow_natCast] at hb
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hy0 _)).2 hb
  rw [Filter.eventually_atTop] at hev
  obtain ⟨a, ha⟩ := hev
  refine ⟨max a 1, le_max_right a 1, fun y hy => ?_⟩
  rw [Real.sqrt_eq_rpow]
  exact ha y (le_trans (le_max_left a 1) hy)

end Commons.Analysis.Real