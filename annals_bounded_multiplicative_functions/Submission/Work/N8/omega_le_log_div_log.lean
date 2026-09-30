import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.n4err_omega_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-- **Bound on the number of distinct prime factors.**
If `1 ≤ q ≤ X ^ (1/δ)` with `X ≥ 1` and `δ > 0`, then
`ω(q) ≤ log X / (δ log 2)`.

This combines `ω(q) ≤ log q / log 2` (since every prime factor is at least `2`)
with `log q ≤ log(X ^ (1/δ)) = (1/δ) log X`. -/
theorem omega_le_log_div_log (X δ : ℝ) (hX : 1 ≤ X) (hδ : 0 < δ) (q : ℕ) (hq : 1 ≤ q)
    (hqX : (q : ℝ) ≤ X ^ (1 / δ)) :
    ((q.primeFactors.card : ℕ) : ℝ) ≤ Real.log X / (δ * Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hq
  -- ω(q) ≤ log q / log 2
  have hω : ((q.primeFactors.card : ℕ) : ℝ) ≤ Real.log q / Real.log 2 :=
    Work.BMF.n4err_omega_le q hq
  -- log q ≤ log(X ^ (1/δ)) = (1/δ) log X = log X / δ
  have hlogq : Real.log q ≤ Real.log X / δ := by
    have h := Real.log_le_log hqpos hqX
    rw [Real.log_rpow hXpos] at h
    simpa [one_div, div_eq_inv_mul] using h
  have hω2 : ((q.primeFactors.card : ℕ) : ℝ) * Real.log 2 ≤ Real.log q :=
    (le_div_iff₀ hlog2).mp hω
  have hlogqδ : Real.log q * δ ≤ Real.log X := (le_div_iff₀ hδ).mp hlogq
  have h1 : ((q.primeFactors.card : ℕ) : ℝ) * Real.log 2 * δ ≤ Real.log q * δ :=
    mul_le_mul_of_nonneg_right hω2 (le_of_lt hδ)
  rw [le_div_iff₀ (by positivity : 0 < δ * Real.log 2)]
  nlinarith [h1, hlogqδ]

end Work.N8
