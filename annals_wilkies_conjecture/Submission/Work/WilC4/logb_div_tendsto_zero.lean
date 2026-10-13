import Mathlib

namespace Work.WilC4

/-- `log_2 β / (β * ρ) → 0` as `β → +∞`, for any fixed `ρ > 0`.
Since `logb 2 β = log β / log 2` and `log 2 ≠ 0`, this is `(1 / log 2)` times the classical
limit `log β / β → 0`, which Mathlib provides as
`Real.tendsto_pow_log_div_mul_add_atTop`. -/
lemma logb_div_tendsto_zero (ρ : ℝ) (hρ : 0 < ρ) :
    Filter.Tendsto (fun β : ℝ => Real.logb 2 β / (β * ρ)) Filter.atTop (nhds 0) := by
  have hlog2 : Real.log 2 ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have hρl : ρ * Real.log 2 ≠ 0 := mul_ne_zero hρ.ne' hlog2
  -- `log β / ((ρ * log 2) * β) → 0`, and this function is exactly the one in the statement.
  have h := Real.tendsto_pow_log_div_mul_add_atTop (ρ * Real.log 2) 0 1 hρl
  simp only [pow_one, add_zero] at h
  refine h.congr' ?_
  filter_upwards with β
  rw [Real.logb]
  field_simp

end Work.WilC4
