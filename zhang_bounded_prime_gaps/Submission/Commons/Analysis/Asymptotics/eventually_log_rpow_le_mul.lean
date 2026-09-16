import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Commons.Analysis.Asymptotics

theorem eventually_log_rpow_le_mul (B : ℝ) (hB : 0 < B) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in Filter.atTop, (Real.log (N : ℝ)) ^ B ≤ c * (N : ℝ) := by
  have h : (fun x : ℝ => Real.log x ^ B) =o[Filter.atTop] fun x : ℝ => x ^ (1 : ℝ) :=
    isLittleO_log_rpow_rpow_atTop B (by norm_num)
  have h2 : (fun N : ℕ => Real.log (N : ℝ) ^ B) =o[Filter.atTop]
      fun N : ℕ => ((N : ℝ) ^ (1 : ℝ)) :=
    h.comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [h2.def hc, Filter.eventually_ge_atTop (1 : ℕ)] with N hN hN1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hN1)) B),
    Real.rpow_one, Real.norm_of_nonneg (Nat.cast_nonneg N)] at hN
  exact hN

end Commons.Analysis.Asymptotics