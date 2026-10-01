import Mathlib

namespace Work.LinnikAreas.DhRepel

/-- Elementary bound: for `t ≥ 900` we have `log t ≤ t / 15`.
This follows from `log t ≤ 2 √t` (Mathlib's `Real.log_le_rpow_div` with exponent `1/2`)
together with `2 √t ≤ t / 15`, which holds as soon as `√t ≥ 30`, i.e. `t ≥ 900`. -/
lemma log_le_div_fifteen {t : ℝ} (ht : 900 ≤ t) : Real.log t ≤ t / 15 := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have h2 : 2 * Real.sqrt t ≤ t / 15 := by
    have hs30 : (30 : ℝ) ≤ Real.sqrt t := by
      have h := Real.sqrt_le_sqrt ht
      rwa [show Real.sqrt 900 = (30 : ℝ) by norm_num] at h
    have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0
    have hkey : 30 * Real.sqrt t ≤ t := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Real.sqrt t)
        (by linarith : (0 : ℝ) ≤ Real.sqrt t - 30), hsq]
    linarith
  have h1 : Real.log t ≤ 2 * Real.sqrt t := by
    have h := Real.log_le_rpow_div ht0 (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at h
    have he : Real.sqrt t / (1 / 2) = 2 * Real.sqrt t := by ring
    linarith
  exact h1.trans h2

/-- For all sufficiently large real `x`, `log log log x ≤ (3/5) log x`, equivalently
`(1/3) log log log x ≤ (1/5) log x`.  This is the elementary threshold that keeps the exponent
`σ = 1 - t/log q` of the Jutila family zero-density estimate inside its range `σ ≥ 4/5` whenever
`t ≤ (1/3) log log log q`. -/
theorem logLogLogDivThreeLeLogDivFive :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      Real.log (Real.log (Real.log x)) / 3 ≤ Real.log x / 5 := by
  refine ⟨Real.exp (Real.exp 900), ?_⟩
  intro x hx
  have hXpos : 0 < Real.exp (Real.exp 900) := Real.exp_pos _
  -- `log x ≥ exp 900`, hence `log log x ≥ 900`
  have hlogx : Real.exp 900 ≤ Real.log x := by
    have := Real.log_le_log hXpos hx
    rwa [Real.log_exp] at this
  have hlogu : (900 : ℝ) ≤ Real.log (Real.log x) := by
    have := Real.log_le_log (Real.exp_pos 900) hlogx
    rwa [Real.log_exp] at this
  -- apply the elementary bound to `t = log log x ≥ 900`
  have hA : Real.log (Real.log (Real.log x)) ≤ Real.log (Real.log x) / 15 :=
    log_le_div_fifteen hlogu
  -- `log log x ≤ log x` for large `x`, in particular `≤ 9 log x`
  have hB : Real.log (Real.log x) ≤ 9 * Real.log x := by
    have h0 : (0 : ℝ) ≤ Real.log x := by have := Real.exp_pos 900; linarith
    have := Real.log_le_self h0
    linarith
  linarith

end Work.LinnikAreas.DhRepel
