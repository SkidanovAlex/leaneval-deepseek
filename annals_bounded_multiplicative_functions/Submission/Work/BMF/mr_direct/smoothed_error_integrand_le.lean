import Mathlib
import Submission.Work.BMF.smoothing_exists

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-- Pointwise bound for the integrand of the smoothed `Λ`-sum error integral.

Given the Vinogradov–Korobov bound for the twisted `Λ`-sum on the *whole* half-line (`hzpt`, with
constants `c₀, C₀ > 0`), the following holds for `A` with `Real.log A ≥ 4`, `T ≥ 3`, `|δ| ≤ 2T` and
`2T ≤ exp((log A / 2)^{21/20})`, and every `t ∈ [0, ⌈4A⌉₊]`:

the weighted error integrand `(deriv bumpFn (t/A))/A · E(t)`, where `E(t)` is the error bracket
`Σ_{n ≤ ⌊t⌋} Λ(n) n^{iδ} − t^{1+iδ}/(1+iδ)`, is bounded in norm by
`(4 C₀ A exp(−c₀ 2^{−1/12} (log A)^{1/12})) · (‖deriv bumpFn (t/A)‖/A)`.

Reason: `deriv bumpFn (t/A) = 0` unless `t/A ∈ [1/4,4]` (endpoints aside).  On `t ∈ [A/4, 4A]` we
have `t ≥ A/4 ≥ 2`, `log t ≥ log A − log 4 ≥ (log A)/2` and `t ≤ 4A`, so `hzpt` applied at `x = t`,
`u = −δ` (legitimate because `|δ| ≤ 2T ≤ exp((log t)^{21/20})`) gives
`‖E(t)‖ ≤ C₀ · 4A · exp(−c₀ ((log A)/2)^{1/12}) = C₀ · 4A · exp(−c₀ 2^{−1/12} (log A)^{1/12})`;
multiplying by `‖deriv bumpFn (t/A)‖/A` and using `A ≥ e^4 > 0` gives the claim.  Outside
`[A/4, 4A]` the left-hand side is `0` because the derivative vanishes. -/
theorem smoothed_error_integrand_le (c₀ C₀ : ℝ) (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hzpt : ∀ x : ℝ, 2 ≤ x → ∀ u : ℝ, |u| ≤ Real.exp ((Real.log x) ^ (21 / 20 : ℝ)) →
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (n : ℂ) ^ (-(Complex.I * u)) - (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖
        ≤ C₀ * x * Real.exp (-c₀ * (Real.log x) ^ (1 / 12 : ℝ)))
    (A T δ t : ℝ) (hA : 4 ≤ Real.log A) (hT : 3 ≤ T) (hδ : |δ| ≤ 2 * T)
    (hTexp : 2 * T ≤ Real.exp (((Real.log A) / 2) ^ (21 / 20 : ℝ)))
    (ht : t ∈ Set.Icc (0 : ℝ) ((⌈4 * A⌉₊ : ℕ) : ℝ)) :
    ‖(((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
        ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (Complex.I * (δ : ℂ)))
          - (t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ)))‖
      ≤ (4 * C₀ * A * Real.exp (-(c₀ * (1 / 2) ^ (1 / 12 : ℝ)) * (Real.log A) ^ (1 / 12 : ℝ))) *
          (‖(deriv Work.BMF.bumpFn (t / A) : ℝ)‖ / A) := by
  rw [Set.mem_Icc] at ht
  -- The derivative of the bump function vanishes outside `[1/4, 4]`; in that case both sides
  -- are zero and there is nothing to prove.
  by_cases hD : deriv Work.BMF.bumpFn (t / A) = 0
  · simp [hD]
  · -- Otherwise `t / A ∈ [1/4, 4]`, so `A > 0` and `t ∈ [A/4, 4A]`.
    have hdivpos : 0 < t / A := by
      by_contra h
      rw [not_lt] at h
      exact hD (Work.BMF.deriv_bumpFn_eq_zero_of_lt (by linarith))
    have hApos : 0 < A := by
      rcases (div_pos_iff.mp hdivpos) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · exact absurd h1 (not_lt.mpr (by linarith [ht.1]))
    have ht_lower : A / 4 ≤ t := by
      by_contra h
      rw [not_le] at h
      exact hD (Work.BMF.deriv_bumpFn_eq_zero_of_lt ((div_lt_iff₀ hApos).mpr (by linarith)))
    have ht_upper : t ≤ 4 * A := by
      by_contra h
      rw [not_le] at h
      exact hD (Work.BMF.deriv_bumpFn_eq_zero_of_gt ((lt_div_iff₀ hApos).mpr h))
    -- `A ≥ e^4 ≥ 8`, hence `t ≥ A / 4 ≥ 2`.
    have hAexp : Real.exp 4 ≤ A := by
      have h := Real.exp_le_exp.mpr hA
      rwa [Real.exp_log hApos] at h
    have hexp8 : (8 : ℝ) ≤ Real.exp 4 := by
      have h3 : (3 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp 2; linarith
      have h4 : Real.exp 4 = (Real.exp 2) ^ 2 := by
        have := Real.exp_nat_mul (2 : ℝ) 2
        norm_num at this
        exact this
      rw [h4]; nlinarith [Real.exp_pos 2]
    have ht2 : (2 : ℝ) ≤ t := by
      have hh : (2 : ℝ) ≤ A / 4 := by linarith
      linarith
    -- `log t ≥ log A - log 4 ≥ (log A) / 2`.
    have hlog4 : Real.log 4 ≤ Real.log A / 2 := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        have := Real.log_pow (2 : ℝ) 2
        norm_num at this
        exact this
      rw [h4]; nlinarith [Real.log_two_lt_d9, hA]
    have hlogt : Real.log A / 2 ≤ Real.log t := by
      have hA4pos : 0 < A / 4 := by linarith
      have hge : Real.log (A / 4) ≤ Real.log t := Real.log_le_log hA4pos ht_lower
      calc Real.log A / 2 = Real.log A - Real.log A / 2 := by ring
        _ ≤ Real.log A - Real.log 4 := by linarith
        _ = Real.log (A / 4) := by rw [Real.log_div hApos.ne' (by norm_num : (4 : ℝ) ≠ 0)]
        _ ≤ Real.log t := hge
    -- Range hypothesis for `hzpt` at `u = -δ`.
    have hδexp : |δ| ≤ Real.exp ((Real.log t) ^ (21 / 20 : ℝ)) := by
      have h1 : |δ| ≤ Real.exp (((Real.log A) / 2) ^ (21 / 20 : ℝ)) := le_trans hδ hTexp
      have h2 : ((Real.log A) / 2) ^ (21 / 20 : ℝ) ≤ (Real.log t) ^ (21 / 20 : ℝ) :=
        Real.rpow_le_rpow (by linarith [hA]) hlogt (by norm_num)
      exact le_trans h1 (Real.exp_le_exp.mpr h2)
    -- The twisted `Λ`-sum bound at `x = t`, `u = -δ`.
    have he1 : Complex.I * (δ : ℂ) = -(Complex.I * (((-δ : ℝ)) : ℂ)) := by push_cast; ring
    have he2 : (1 + Complex.I * (δ : ℂ)) = (1 - Complex.I * (((-δ : ℝ)) : ℂ)) := by push_cast; ring
    have hz := hzpt t ht2 (-δ) (by simpa using hδexp)
    rw [← he2, ← he1] at hz
    -- Comparison of the two exponentials: `(log A / 2)^{1/12} = 2^{-1/12} (log A)^{1/12}`.
    have hSS : Real.exp (-c₀ * (Real.log t) ^ (1 / 12 : ℝ))
        ≤ Real.exp (-(c₀ * (1 / 2) ^ (1 / 12 : ℝ)) * (Real.log A) ^ (1 / 12 : ℝ)) := by
      rw [Real.exp_le_exp]
      have h1 : ((Real.log A) / 2) ^ (1 / 12 : ℝ) ≤ (Real.log t) ^ (1 / 12 : ℝ) :=
        Real.rpow_le_rpow (by linarith [hA]) hlogt (by norm_num)
      have h2 : ((Real.log A) / 2) ^ (1 / 12 : ℝ)
          = (1 / 2) ^ (1 / 12 : ℝ) * (Real.log A) ^ (1 / 12 : ℝ) := by
        rw [show (Real.log A) / 2 = (1 / 2) * Real.log A by ring,
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) (by linarith [hA])]
      have h3 : c₀ * ((1 / 2) ^ (1 / 12 : ℝ) * (Real.log A) ^ (1 / 12 : ℝ))
          ≤ c₀ * (Real.log t) ^ (1 / 12 : ℝ) :=
        mul_le_mul_of_nonneg_left (h2 ▸ h1) (le_of_lt hc₀)
      nlinarith [h3]
    -- The bracket is bounded by the claimed constant.
    have hmain : ‖((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (Complex.I * (δ : ℂ)))
          - (t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ)))‖
        ≤ 4 * C₀ * A * Real.exp (-(c₀ * (1 / 2) ^ (1 / 12 : ℝ)) * (Real.log A) ^ (1 / 12 : ℝ)) := by
      have h1 : C₀ * t ≤ C₀ * (4 * A) := mul_le_mul_of_nonneg_left ht_upper (le_of_lt hC₀)
      have h2 : C₀ * t * Real.exp (-c₀ * (Real.log t) ^ (1 / 12 : ℝ))
          ≤ (C₀ * (4 * A)) *
            Real.exp (-(c₀ * (1 / 2) ^ (1 / 12 : ℝ)) * (Real.log A) ^ (1 / 12 : ℝ)) :=
        mul_le_mul h1 hSS (le_of_lt (Real.exp_pos _))
          (by nlinarith [le_of_lt hC₀, le_of_lt hApos])
      calc ‖((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (Complex.I * (δ : ℂ)))
          - (t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ)))‖
          ≤ C₀ * t * Real.exp (-c₀ * (Real.log t) ^ (1 / 12 : ℝ)) := hz
        _ ≤ (C₀ * (4 * A)) *
              Real.exp (-(c₀ * (1 / 2) ^ (1 / 12 : ℝ)) * (Real.log A) ^ (1 / 12 : ℝ)) := h2
        _ = 4 * C₀ * A *
              Real.exp (-(c₀ * (1 / 2) ^ (1 / 12 : ℝ)) * (Real.log A) ^ (1 / 12 : ℝ)) := by ring
    -- Multiply by `‖deriv bumpFn (t/A)‖ / A`.
    have hnormA : ‖(A : ℂ)‖ = A := by simp [abs_of_pos hApos]
    have hLHS : ‖(((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
        ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (Complex.I * (δ : ℂ)))
          - (t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ)))‖
        = (‖(deriv Work.BMF.bumpFn (t / A) : ℝ)‖ / A) *
          ‖((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (Complex.I * (δ : ℂ)))
          - (t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ)))‖ := by
      rw [norm_mul, norm_div, hnormA]; simp
    rw [hLHS]
    calc (‖(deriv Work.BMF.bumpFn (t / A) : ℝ)‖ / A) *
          ‖((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (Complex.I * (δ : ℂ)))
          - (t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ)))‖
        ≤ (‖(deriv Work.BMF.bumpFn (t / A) : ℝ)‖ / A) *
          (4 * C₀ * A *
            Real.exp (-(c₀ * (1 / 2) ^ (1 / 12 : ℝ)) * (Real.log A) ^ (1 / 12 : ℝ))) :=
        mul_le_mul_of_nonneg_left hmain (div_nonneg (norm_nonneg _) (le_of_lt hApos))
      _ = (4 * C₀ * A *
            Real.exp (-(c₀ * (1 / 2) ^ (1 / 12 : ℝ)) * (Real.log A) ^ (1 / 12 : ℝ))) *
          (‖(deriv Work.BMF.bumpFn (t / A) : ℝ)‖ / A) := by ring

end Work.BMF.mr_direct
