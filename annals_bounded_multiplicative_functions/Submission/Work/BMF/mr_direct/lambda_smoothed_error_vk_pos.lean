import Mathlib
import Submission.Work.BMF.smoothing_exists
import Submission.Work.BMF.zeta_prime_sum_twist
import Submission.Work.BMF.mr_direct.deriv_bumpFn_weighted_integral_eq
import Submission.Work.BMF.mr_direct.smoothed_error_integrand_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open MeasureTheory

/-!
# The Vinogradov–Korobov bound for the error integral of the smoothed `Λ`-sum

The statement requested as `Work.BMF.mr_direct.lambda_smoothed_error_vk` is **false** as written:
its hypothesis is `4 ≤ Real.log A`, and Mathlib's `Real.log` is the *even* function `log |x|`
(`Real.log_neg_eq_log`), so `A < 0` is allowed.  For `A = -exp 10` all the hypotheses hold
(`Real.log A = 10 ≥ 4`, `T = 3`, `δ = 0`), while `⌈4 * A⌉₊ = 0`, so the integral collapses to `0`
and the right-hand side `C * A * exp (…)` is *negative*.  This is formalised below as
`lambda_smoothed_error_vk_statement_false`.

The intended statement (the one a large `A` satisfies, and the one proved in this file) replaces
the hypothesis `4 ≤ Real.log A` by `0 < A` together with `4 ≤ Real.log A` — equivalently by
`Real.exp 4 ≤ A`.
-/

/-- **The literally stated lemma is false**: `4 ≤ Real.log A` does not force `A > 0` in Mathlib.

Counterexample: `A = -exp 10`, `T = 3`, `δ = 0`.  Then `Real.log A = 10`, `⌈4 * A⌉₊ = 0`, so the
integral over `0..0` vanishes, while `C * A * exp (…) < 0`. -/
theorem lambda_smoothed_error_vk_statement_false :
    ¬ (∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (A T δ : ℝ), 4 ≤ Real.log A → 3 ≤ T → |δ| ≤ 2 * T →
        2 * T ≤ Real.exp (((Real.log A) / 2) ^ (21 / 20 : ℝ)) →
        ‖∫ t in (0 : ℝ)..(((⌈4 * A⌉₊ : ℕ) : ℝ)),
            (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
              ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                  (n : ℂ) ^ (Complex.I * (δ : ℂ)))
                - (t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ)))‖
          ≤ C * A * Real.exp (-c * (Real.log A) ^ (1 / 12 : ℝ))) := by
  rintro ⟨c, C, hc, hC, h⟩
  set A : ℝ := -(Real.exp 10) with hAdef
  have hlog : Real.log A = 10 := by rw [hAdef, Real.log_neg_eq_log, Real.log_exp]
  have hA4 : 4 ≤ Real.log A := by rw [hlog]; norm_num
  have hceil : ⌈(4 : ℝ) * A⌉₊ = 0 := by
    refine Nat.eq_zero_of_le_zero (Nat.ceil_le.mpr ?_)
    rw [hAdef]; nlinarith [Real.exp_pos 10]
  have hTexp : 2 * 3 ≤ Real.exp (((Real.log A) / 2) ^ (21 / 20 : ℝ)) := by
    rw [hlog]
    have h54 : ((10 : ℝ) / 2) = 5 := by norm_num
    rw [h54]
    have h5 : (5 : ℝ) ≤ (5 : ℝ) ^ (21 / 20 : ℝ) := by
      have h1 : (5 : ℝ) ^ (21 / 20 : ℝ) = 5 ^ (1 : ℝ) * 5 ^ (1 / 20 : ℝ) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 5)]; norm_num
      rw [h1, Real.rpow_one]
      have h2 : 1 ≤ (5 : ℝ) ^ (1 / 20 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
      linarith
    calc (2 * 3 : ℝ) = 5 + 1 := by norm_num
      _ ≤ Real.exp 5 := Real.add_one_le_exp 5
      _ ≤ Real.exp ((5 : ℝ) ^ (21 / 20 : ℝ)) := Real.exp_le_exp.mpr h5
  have hδ : |(0 : ℝ)| ≤ 2 * 3 := by norm_num
  have hmain := h A 3 0 hA4 (by norm_num) hδ hTexp
  have hceil' : (((⌈4 * A⌉₊ : ℕ) : ℝ)) = 0 := by rw [hceil]; norm_num
  rw [hceil'] at hmain
  have hL : ‖∫ t in (0 : ℝ)..(0 : ℝ),
      (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
        ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (Complex.I * ((0 : ℝ) : ℂ)))
          - (t : ℂ) ^ (1 + Complex.I * ((0 : ℝ) : ℂ)) /
              (1 + Complex.I * ((0 : ℝ) : ℂ)))‖ = 0 := by
    simp
  have hAneg : A < 0 := by rw [hAdef]; linarith [Real.exp_pos 10]
  have hexp : 0 < Real.exp (-c * (Real.log A) ^ (1 / 12 : ℝ)) := Real.exp_pos _
  have hR : C * A * Real.exp (-c * (Real.log A) ^ (1 / 12 : ℝ)) < 0 := by
    have h1 : C * A * Real.exp (-c * (Real.log A) ^ (1 / 12 : ℝ))
        = (C * Real.exp (-c * (Real.log A) ^ (1 / 12 : ℝ))) * A := by ring
    rw [h1]
    exact mul_neg_of_pos_of_neg (mul_pos hC hexp) hAneg
  rw [hL] at hmain
  linarith

/-- **The Vinogradov–Korobov bound for the error integral of the smoothed `Λ`-sum**, with the
hypothesis made precise: `A` must be positive and `Real.log A ≥ 4` (equivalently
`Real.exp 4 ≤ A`), which is exactly the range in which `Work.BMF.zeta_prime_sum_twist` is applied
with `x = t` for `t ∈ [A/4, 4A]`.

For `A > 0`, `T ≥ 3`, `|δ| ≤ 2T` and `2T ≤ exp(((log A)/2)^{21/20})`,
`‖∫_0^{⌈4A⌉₊} (deriv bumpFn (t/A))/A · E(t) dt‖ ≤ C A exp(−c (log A)^{1/12})`,
where `E(t) = Σ_{n ≤ ⌊t⌋} Λ(n) n^{iδ} − t^{1+iδ}/(1+iδ)`.

Route: the integrand vanishes unless `t/A ∈ [1/4,4]`, i.e. `t ∈ [A/4,4A]`; there `log t ≥ (log A)/2`
and `t ≤ 4A`, so `Work.BMF.zeta_prime_sum_twist` at `x = t`, `u = -δ` gives the pointwise bound
`‖E(t)‖ ≤ 4 C₀ A exp(−c₀ ((log A)/2)^{1/12})`
(`Work.BMF.mr_direct.smoothed_error_integrand_le`); integrating against
`‖(deriv bumpFn (t/A))/A‖` and substituting `t = A s` turns the weight integral into the constant
`∫_0^4 ‖deriv bumpFn s‖ ds` (`Work.BMF.mr_direct.deriv_bumpFn_weighted_integral_eq`). -/
theorem lambda_smoothed_error_vk_pos :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (A T δ : ℝ), 0 < A → 4 ≤ Real.log A → 3 ≤ T → |δ| ≤ 2 * T →
        2 * T ≤ Real.exp (((Real.log A) / 2) ^ (21 / 20 : ℝ)) →
        ‖∫ t in (0 : ℝ)..(((⌈4 * A⌉₊ : ℕ) : ℝ)),
            (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
              ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                  (n : ℂ) ^ (Complex.I * (δ : ℂ)))
                - (t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ)))‖
          ≤ C * A * Real.exp (-c * (Real.log A) ^ (1 / 12 : ℝ)) := by
  -- the Vinogradov–Korobov input for the twisted `Λ`-sum, with a certified positive constant
  obtain ⟨c₀, C₀₀, hc₀, hzpt₀⟩ := Work.BMF.zeta_prime_sum_twist
  set C₀ : ℝ := |C₀₀| + 1 with hC₀def
  have hC₀pos : 0 < C₀ := by rw [hC₀def]; positivity
  have hC₀le : C₀₀ ≤ C₀ := by rw [hC₀def]; linarith [le_abs_self C₀₀]
  have hzpt : ∀ x : ℝ, 2 ≤ x → ∀ u : ℝ, |u| ≤ Real.exp ((Real.log x) ^ (21 / 20 : ℝ)) →
      ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          (n : ℂ) ^ (-(Complex.I * u)) - (x : ℂ) ^ (1 - Complex.I * u) / (1 - Complex.I * u)‖
        ≤ C₀ * x * Real.exp (-c₀ * (Real.log x) ^ (1 / 12 : ℝ)) := by
    intro x hx u hu
    refine le_trans (hzpt₀ x hx u hu) ?_
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have hexp : 0 ≤ Real.exp (-c₀ * (Real.log x) ^ (1 / 12 : ℝ)) := Real.exp_nonneg _
    have h1 : C₀₀ * x ≤ C₀ * x := mul_le_mul_of_nonneg_right hC₀le hx0
    exact mul_le_mul_of_nonneg_right h1 hexp
  -- the two constants of the final bound
  set K : ℝ := ∫ s in (0 : ℝ)..4, ‖(deriv Work.BMF.bumpFn s : ℝ)‖ with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun s _ => norm_nonneg _)
  set c : ℝ := c₀ * (1 / 2 : ℝ) ^ (1 / 12 : ℝ) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  refine ⟨c, 4 * C₀ * (K + 1), hcpos, by nlinarith, ?_⟩
  intro A T δ hApos hlogA hT hδ hTexp
  set N : ℝ := ((⌈4 * A⌉₊ : ℕ) : ℝ) with hNdef
  have hAN : 4 * A ≤ N := by rw [hNdef]; exact Nat.le_ceil (4 * A)
  have hN0 : 0 ≤ N := by linarith
  have hderiv_cont : Continuous (deriv Work.BMF.bumpFn) :=
    (Work.BMF.bumpFn_contDiff 1).continuous_deriv (by norm_num)
  have hnormcont : Continuous (fun t : ℝ => ‖(deriv Work.BMF.bumpFn (t / A) : ℝ)‖) :=
    hderiv_cont.norm.comp (continuous_id.div_const A)
  -- step 1: put the norm inside the integral
  have hstep1 : ‖∫ t in (0 : ℝ)..N,
        (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
          ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              (n : ℂ) ^ (Complex.I * (δ : ℂ)))
            - (t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ)))‖
      ≤ ∫ t in (0 : ℝ)..N,
        ‖(((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
          ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              (n : ℂ) ^ (Complex.I * (δ : ℂ)))
            - (t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ)))‖ :=
    intervalIntegral.norm_integral_le_integral_norm hN0
  -- step 2: the pointwise bound, integrated
  have hstep2 : (∫ t in (0 : ℝ)..N,
        ‖(((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
          ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              (n : ℂ) ^ (Complex.I * (δ : ℂ)))
            - (t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ)))‖)
      ≤ ∫ t in (0 : ℝ)..N,
          (4 * C₀ * A *
              Real.exp (-(c₀ * (1 / 2) ^ (1 / 12 : ℝ)) * (Real.log A) ^ (1 / 12 : ℝ))) *
            (‖(deriv Work.BMF.bumpFn (t / A) : ℝ)‖ / A) := by
    rw [intervalIntegral.integral_of_le hN0, intervalIntegral.integral_of_le hN0]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => norm_nonneg _) ?_ ?_
    · have hii : IntervalIntegrable
          (fun t : ℝ => (4 * C₀ * A *
              Real.exp (-(c₀ * (1 / 2) ^ (1 / 12 : ℝ)) * (Real.log A) ^ (1 / 12 : ℝ))) *
            (‖(deriv Work.BMF.bumpFn (t / A) : ℝ)‖ / A)) volume 0 N :=
        (continuous_const.mul (hnormcont.div_const A)).intervalIntegrable 0 N
      simpa only [IntervalIntegrable, IntegrableOn, Set.uIoc_of_le hN0] using hii.1
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc ?_
      intro t ht
      exact smoothed_error_integrand_le c₀ C₀ hc₀ hC₀pos hzpt A T δ t hlogA hT hδ hTexp
        ⟨le_of_lt ht.1, ht.2⟩
  -- step 3: factor out the constant and use the change of variables
  have hK_eq : (∫ t in (0 : ℝ)..N, ‖(deriv Work.BMF.bumpFn (t / A) : ℝ)‖ / A) = K := by
    rw [hKdef]
    exact deriv_bumpFn_weighted_integral_eq A N hApos hAN
  have hstep3 : (∫ t in (0 : ℝ)..N,
          (4 * C₀ * A *
              Real.exp (-(c₀ * (1 / 2) ^ (1 / 12 : ℝ)) * (Real.log A) ^ (1 / 12 : ℝ))) *
            (‖(deriv Work.BMF.bumpFn (t / A) : ℝ)‖ / A))
      = (4 * C₀ * A *
          Real.exp (-(c₀ * (1 / 2) ^ (1 / 12 : ℝ)) * (Real.log A) ^ (1 / 12 : ℝ))) * K := by
    rw [intervalIntegral.integral_const_mul, hK_eq]
  -- step 4: the final constant bookkeeping
  have hexp_eq : Real.exp (-(c₀ * (1 / 2) ^ (1 / 12 : ℝ)) * (Real.log A) ^ (1 / 12 : ℝ))
      = Real.exp (-c * (Real.log A) ^ (1 / 12 : ℝ)) := by
    rw [hcdef]
  have hstep4 : (4 * C₀ * A *
        Real.exp (-(c₀ * (1 / 2) ^ (1 / 12 : ℝ)) * (Real.log A) ^ (1 / 12 : ℝ))) * K
      ≤ 4 * C₀ * (K + 1) * A * Real.exp (-c * (Real.log A) ^ (1 / 12 : ℝ)) := by
    rw [hexp_eq]
    have hcoef : 0 ≤ 4 * C₀ * A * Real.exp (-c * (Real.log A) ^ (1 / 12 : ℝ)) := by positivity
    calc (4 * C₀ * A * Real.exp (-c * (Real.log A) ^ (1 / 12 : ℝ))) * K
        ≤ (4 * C₀ * A * Real.exp (-c * (Real.log A) ^ (1 / 12 : ℝ))) * (K + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hcoef
      _ = 4 * C₀ * (K + 1) * A * Real.exp (-c * (Real.log A) ^ (1 / 12 : ℝ)) := by ring
  calc ‖∫ t in (0 : ℝ)..N,
        (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
          ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              (n : ℂ) ^ (Complex.I * (δ : ℂ)))
            - (t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ)))‖
      ≤ _ := hstep1
    _ ≤ _ := hstep2
    _ = _ := hstep3
    _ ≤ _ := hstep4

end Work.BMF.mr_direct
