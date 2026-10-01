import Mathlib

set_option linter.unusedVariables false

namespace Work.LinnikAreas2

open Filter

/-- For `σ : ℝ`, `0 < B < A` and `c ≥ 0`, the sequence
`(1 + c·N) · (N+1)^(σ-1) · (exp(-(N+1)/A) - exp(-(N+1)/B))` tends to `0`.

Since `0 < B < A` we have `0 ≤ exp(-(N+1)/A) - exp(-(N+1)/B) ≤ exp(-(N+1)/A)`,
and `(1 + c·N)·(N+1)^(σ-1) ≤ (1+c)·(N+1)^σ`; the bound
`(1+c)·(N+1)^σ·exp(-(N+1)/A)` is a constant multiple of
`x^σ·exp(-x/A)` at `x = N+1`, which tends to `0`. -/
theorem thetaF_mul_tendsto_zero {σ A B c : ℝ} (hσ : 0 < σ) (hB : 0 < B) (hBA : B < A)
    (hc : 0 ≤ c) :
    Filter.Tendsto (fun N : ℕ => (1 + c*(N:ℝ)) * ((N+1 : ℕ):ℝ)^(σ-1) *
      (Real.exp (-(((N+1 : ℕ):ℝ)/A)) - Real.exp (-(((N+1 : ℕ):ℝ)/B))))
      Filter.atTop (nhds 0) := by
  have hA : 0 < A := lt_trans hB hBA
  -- `N + 1 → ∞`
  have ht : Tendsto (fun N : ℕ => ((N+1 : ℕ):ℝ)) atTop atTop := by
    have h : Tendsto (fun N : ℕ => (N:ℝ) + 1) atTop atTop :=
      Filter.tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop
    simpa only [Nat.cast_add, Nat.cast_one] using h
  -- the model limit `x^σ · exp(-x/A) → 0`, composed with `N ↦ N+1`
  have hkey : Tendsto (fun N : ℕ => ((N+1 : ℕ):ℝ)^σ * Real.exp (-(((N+1 : ℕ):ℝ)/A)))
      atTop (nhds 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero σ (1/A) (by positivity)).comp ht
    refine Filter.Tendsto.congr' ?_ h
    filter_upwards with N
    simp only [Function.comp_apply]
    rw [show -(1/A) * ((N+1 : ℕ):ℝ) = -(((N+1 : ℕ):ℝ)/A) by ring]
  -- the dominating sequence
  have hg : Tendsto (fun N : ℕ => (1+c) * (((N+1 : ℕ):ℝ)^σ * Real.exp (-(((N+1 : ℕ):ℝ)/A))))
      atTop (nhds 0) := by
    simpa using hkey.const_mul (1+c)
  refine squeeze_zero (fun N => ?_) (fun N => ?_) hg
  · -- non-negativity
    set t : ℝ := ((N+1 : ℕ):ℝ) with htdef
    have htpos : 0 < t := by rw [htdef]; positivity
    have h1 : (1:ℝ)/A ≤ 1/B := one_div_le_one_div_of_le hB (le_of_lt hBA)
    have h2 : t/A ≤ t/B := by
      have := mul_le_mul_of_nonneg_left h1 htpos.le
      simpa [div_eq_mul_inv] using this
    have h3 : Real.exp (-(t/B)) ≤ Real.exp (-(t/A)) := by
      apply Real.exp_le_exp.mpr; linarith
    have hd : 0 ≤ Real.exp (-(t/A)) - Real.exp (-(t/B)) := by linarith
    exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg htpos.le _)) hd
  · -- upper bound
    set t : ℝ := ((N+1 : ℕ):ℝ) with htdef
    have htpos : 0 < t := by rw [htdef]; positivity
    have ht_eq : t = (N:ℝ) + 1 := by rw [htdef]; push_cast; ring
    -- `1 + c·N ≤ (1+c)·(N+1)`
    have hu : (1 + c*(N:ℝ)) ≤ (1+c)*t := by
      rw [ht_eq]; nlinarith [hc, (Nat.cast_nonneg N : (0:ℝ) ≤ (N:ℝ))]
    -- `t · t^(σ-1) = t^σ`
    have hpow : t * t^(σ-1) = t^σ := by
      have hh := Real.rpow_add htpos (σ - 1) 1
      rw [show σ - 1 + 1 = σ by ring, Real.rpow_one] at hh
      rw [hh]; exact mul_comm _ _
    have hu2 : (1 + c*(N:ℝ))*t^(σ-1) ≤ (1+c)*t^σ := by
      have hv : 0 ≤ t^(σ-1) := Real.rpow_nonneg htpos.le _
      calc (1 + c*(N:ℝ))*t^(σ-1)
          ≤ ((1+c)*t)*t^(σ-1) := mul_le_mul_of_nonneg_right hu hv
        _ = (1+c)*(t*t^(σ-1)) := by rw [mul_assoc]
        _ = (1+c)*t^σ := by rw [hpow]
    have h1 : (1:ℝ)/A ≤ 1/B := one_div_le_one_div_of_le hB (le_of_lt hBA)
    have h2 : t/A ≤ t/B := by
      have := mul_le_mul_of_nonneg_left h1 htpos.le
      simpa [div_eq_mul_inv] using this
    have hdnonneg : 0 ≤ Real.exp (-(t/A)) - Real.exp (-(t/B)) := by
      have h3 : Real.exp (-(t/B)) ≤ Real.exp (-(t/A)) := by
        apply Real.exp_le_exp.mpr; linarith
      linarith
    have hd : Real.exp (-(t/A)) - Real.exp (-(t/B)) ≤ Real.exp (-(t/A)) := by
      have := Real.exp_pos (-(t/B)); linarith
    have hb : 0 ≤ (1+c)*t^σ := mul_nonneg (by linarith) (Real.rpow_nonneg htpos.le _)
    calc (1 + c*(N:ℝ)) * t^(σ-1) * (Real.exp (-(t/A)) - Real.exp (-(t/B)))
        ≤ ((1+c)*t^σ) * Real.exp (-(t/A)) := mul_le_mul hu2 hd hdnonneg hb
      _ = (1+c) * (t^σ * Real.exp (-(t/A))) := by ring

end Work.LinnikAreas2
