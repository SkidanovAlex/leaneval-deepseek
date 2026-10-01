import Mathlib

namespace Work.ZeroFreeTables.OffAxis

/-- Height bound used in the zero-free region argument: if the logarithm of the
modulus `q` dominates `6 log T`, then the power `(q*T)^(6/log q)` is at most
`exp 7`.

Indeed, writing `a = 6 / log q`, the exponent in `(q*T)^a = exp(a * log(q*T))`
splits as `a * log q + a * log T = 6 + a * log T`, and `a * log T = 6 log T / log q ≤ 1`
by the hypothesis. -/
theorem rpow_height_bound {q : ℕ} {T : ℝ} (hq : 1 < q) (hT : 1 ≤ T)
    (hlog : 6 * Real.log T ≤ Real.log (q : ℝ)) :
    ((q : ℝ) * T) ^ (6 / Real.log (q : ℝ)) ≤ Real.exp 7 := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := lt_trans zero_lt_one hq1
  have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hbase_pos : 0 < (q : ℝ) * T := mul_pos hqpos hTpos
  rw [Real.rpow_def_of_pos hbase_pos, Real.log_mul (ne_of_gt hqpos) (ne_of_gt hTpos)]
  apply Real.exp_le_exp.mpr
  have h1 : Real.log (q : ℝ) * (6 / Real.log (q : ℝ)) = 6 := by field_simp
  have h2 : Real.log T * (6 / Real.log (q : ℝ)) ≤ 1 := by
    have hh : Real.log T * (6 / Real.log (q : ℝ)) = (6 * Real.log T) / Real.log (q : ℝ) := by
      ring
    rw [hh]
    exact (div_le_one hlogq_pos).mpr hlog
  rw [add_mul, h1]
  linarith [h2]

end Work.ZeroFreeTables.OffAxis
