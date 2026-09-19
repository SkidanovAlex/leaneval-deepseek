import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Submission.Commons.Analysis.Asymptotics.eventually_log_rpow_le_mul

namespace Commons.Analysis.Asymptotics

/-- For positive exponents `r, s` and a positive constant `c`, eventually
`(log n)^r ≤ c * n^s` along the naturals. -/
theorem log_rpow_le_const_mul_rpow {r s c : ℝ} (hr : 0 < r) (hs : 0 < s) (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop, (Real.log (n:ℝ)) ^ r ≤ c * (n:ℝ) ^ s := by
  have h : (fun x : ℝ => Real.log x ^ r) =o[Filter.atTop] fun x : ℝ => x ^ s :=
    isLittleO_log_rpow_rpow_atTop r hs
  have h2 : (fun n : ℕ => Real.log (n : ℝ) ^ r) =o[Filter.atTop]
      fun n : ℕ => ((n : ℝ) ^ s) :=
    h.comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [h2.def hc, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hn1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast hn1)) r),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) s)] at hn
  exact hn

end Commons.Analysis.Asymptotics
