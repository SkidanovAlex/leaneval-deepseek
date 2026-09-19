import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Submission.Commons.Analysis.Complex.rectZeroCount_boundary_le

namespace Commons.Analysis.ExpLog

/-- For any constant `K ≥ 0`, any natural power `n`, and any positive exponent `r`,
`K * (log x)^n ≤ x^r` for all sufficiently large real `x`. -/
theorem const_mul_log_pow_le_rpow_threshold {K : ℝ} (hK : 0 ≤ K) {n : ℕ} {r : ℝ} (hr : 0 < r) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → K * (Real.log x) ^ n ≤ x ^ r := by
  -- Little-o: `(log x)^n = o(x^r)` as `x → ∞`.
  have hbase : (fun x : ℝ => Real.log x ^ (n : ℝ)) =o[Filter.atTop] (fun x : ℝ => x ^ r) :=
    isLittleO_log_rpow_rpow_atTop (n : ℝ) hr
  have hK' : (fun x : ℝ => K * Real.log x ^ (n : ℝ)) =o[Filter.atTop] (fun x : ℝ => x ^ r) :=
    hbase.const_mul_left K
  -- Convert the norm bound into the desired eventual inequality, on `x ≥ 1`.
  have hev : ∀ᶠ x : ℝ in Filter.atTop, K * (Real.log x) ^ n ≤ x ^ r := by
    filter_upwards [hK'.eventuallyLE, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hpow_nonneg : 0 ≤ Real.log x ^ (n : ℝ) := Real.rpow_nonneg hlog_nonneg _
    have hx_nonneg : 0 ≤ x := le_trans zero_le_one hx1
    rw [Real.norm_of_nonneg (mul_nonneg hK hpow_nonneg),
        Real.norm_of_nonneg (Real.rpow_nonneg hx_nonneg r)] at hx
    rwa [Real.rpow_natCast] at hx
  -- Read the threshold off of the eventual statement and clamp it to be `≥ 1`.
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max a 1, le_max_right _ _, ?_⟩
  intro x hx
  exact ha x (le_trans (le_max_left _ _) hx)

end Commons.Analysis.ExpLog