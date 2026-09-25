import Submission.Work.RHContract.MarginDefs
import Submission.Work.RHContract.A.ca_margin_lower
import Submission.Work.RHContract.A.psiTail_ge_of_RH
import Submission.Commons.NumberTheory.Chebyshev.theta_lower_ninetenths

/-!
# `Work.RHContract.A.RegionIIIFromMargin` — Region III from Lemma M, A1 and the margin inequality

Once the margin lemma (`A.ca_margin_lower`, Lemma M) and the `J`-lower bound
(`A.psiTail_ge_of_RH`, A1) are in hand, Region III reduces to the purely arithmetic
inequality

`c_J(ξ)·u(ξ) ≤ C₁ + Net₂ − W − K₃`,
`c_J(ξ) = β(5 + 7/L + 4/L²) + log(2π)/√ξ + 1/ξ`, `u(ξ) = 1/(√ξ L)`, `β = 2 + γ − log 4π`,
`ξ = ξ(ε)`, `L = log ξ`,

which is the content of `A.regionIII_margin_positive`.  Indeed
`Δ(N) := γ + logloglog N − log(σ(N)/N) ≥ J(ξ) + C₁ + Net₂ − W − K₃ ≥ −c_J·u + c_J·u = 0`,
and `Δ(N) ≥ 0` is Robin's inequality at `N = caNumber ε`.

This module also shows that any `ξ ≥ 10^8` forces `log N_ε ≥ 9·10^7` (via
`A.ca_delta_nonneg` and `θ(ξ) ≥ 0.9ξ`), which is what makes the two `log log`s positive.
-/

open scoped ArithmeticFunction.sigma

namespace Work.RHContract

noncomputable section

/-- For `ξ(ε) ≥ 10^8` the colossally abundant number is huge: `9·10^7 ≤ log N_ε`, hence
`N_ε > 1` and both `log N_ε` and `log log N_ε` are `> 1`. -/
theorem log_caNumber_ge_of_large (ε : ℝ) (hε : 0 < ε)
    (hξ : (10 : ℝ) ^ 8 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    (9 : ℝ) * 10 ^ 7 ≤ Real.log (Work.RHPlan.caNumber ε : ℝ) := by
  have hψ : Chebyshev.psi (Work.RHPlan.caXi ε : ℝ) ≤ Real.log (Work.RHPlan.caNumber ε : ℝ) := by
    have := Work.RHContract.A.ca_delta_nonneg ε hε (le_trans (by norm_num) hξ)
    linarith
  have hθ : (9 / 10 : ℝ) * (Work.RHPlan.caXi ε : ℝ) ≤ Chebyshev.psi (Work.RHPlan.caXi ε : ℝ) :=
    le_trans (Commons.NumberTheory.Chebyshev.theta_lower_ninetenths _
        (le_trans (by norm_num) hξ)) (Chebyshev.theta_le_psi _)
  have : (9 / 10 : ℝ) * (10 : ℝ) ^ 8 ≤ (9 / 10 : ℝ) * (Work.RHPlan.caXi ε : ℝ) := by
    nlinarith
  nlinarith

/-- **Region III, conditional on the arithmetic margin inequality.**  Under RH, for `ξ(ε) ≥ 10^8`,
if the arithmetic side of ROUTE_LEAD §2.4 dominates the `J`-bound of A1 then Robin's
inequality holds at `caNumber ε`.

Instantiating `hmargin` with `A.regionIII_margin_positive h ε hε hξ` gives
`robin_ca_regionIII`. -/
theorem robin_ca_regionIII_of_marginPositive (h : RiemannHypothesis) (ε : ℝ) (hε : 0 < ε)
    (hξ : (10 : ℝ) ^ 8 ≤ (Work.RHPlan.caXi ε : ℝ))
    (hmargin : ((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi))
        * (5 + 7 / Real.log (Work.RHPlan.caXi ε : ℝ)
            + 4 / (Real.log (Work.RHPlan.caXi ε : ℝ)) ^ 2)
      + Real.log (2 * Real.pi) / Real.sqrt (Work.RHPlan.caXi ε : ℝ)
      + 1 / (Work.RHPlan.caXi ε : ℝ))
    / (Real.sqrt (Work.RHPlan.caXi ε : ℝ) * Real.log (Work.RHPlan.caXi ε : ℝ))
    ≤ Work.RHContract.Margin.caC1 ε + Work.RHContract.Margin.caNet2 ε
        - Work.RHContract.Margin.caW ε - Work.RHContract.Margin.caK3 ε) :
    Work.RHPlan.RobinBound (Work.RHPlan.caNumber ε) := by
  have hξ' : (1530 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := le_trans (by norm_num) hξ
  have hM := Work.RHContract.A.ca_margin_lower ε hε hξ'
  have hA1 := Work.RHContract.A.psiTail_ge_of_RH h (Work.RHPlan.caXi ε : ℝ)
    (le_trans (by norm_num) hξ)
  rw [neg_div] at hA1
  have hnonneg : (0 : ℝ) ≤ Real.eulerMascheroniConstant
      + Real.log (Real.log (Real.log (Work.RHPlan.caNumber ε)))
      - Real.log (((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ) /
          (Work.RHPlan.caNumber ε : ℝ)) := by
    linarith
  have hlogN : (1 : ℝ) < Real.log (Work.RHPlan.caNumber ε : ℝ) := by
    have := log_caNumber_ge_of_large ε hε hξ
    linarith
  have hloglogNpos : 0 < Real.log (Real.log (Work.RHPlan.caNumber ε : ℝ)) := Real.log_pos hlogN
  have hNposnat : (0 : ℕ) < Work.RHPlan.caNumber ε := by
    by_contra hc
    have h0 : Work.RHPlan.caNumber ε = 0 := by omega
    rw [h0] at hlogN
    norm_num at hlogN
  have hNpos : (0 : ℝ) < (Work.RHPlan.caNumber ε : ℝ) := by exact_mod_cast hNposnat
  have hNgt1 : (1 : ℝ) < (Work.RHPlan.caNumber ε : ℝ) := by
    have hexp : Real.exp 1 < (Work.RHPlan.caNumber ε : ℝ) := by
      have h' := Real.exp_lt_exp.mpr hlogN
      rwa [Real.exp_log hNpos] at h'
    linarith [Real.exp_one_gt_two, hexp]
  have hσpos : (0 : ℝ) < ((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ) := by
    exact_mod_cast (ArithmeticFunction.sigma_pos_iff).2 hNposnat
  have hratio : 0 < ((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ) /
      (Work.RHPlan.caNumber ε : ℝ) := div_pos hσpos hNpos
  have hle : Real.log (((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ) /
      (Work.RHPlan.caNumber ε : ℝ))
      ≤ Real.eulerMascheroniConstant + Real.log (Real.log (Real.log (Work.RHPlan.caNumber ε))) := by
    linarith
  have hexp := Real.exp_le_exp.mpr hle
  rw [Real.exp_log hratio, Real.exp_add, Real.exp_log hloglogNpos] at hexp
  rw [Work.RHPlan.RobinBound]
  have hmul := mul_le_mul_of_nonneg_right hexp (le_of_lt hNpos)
  have heq : (((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ) /
        (Work.RHPlan.caNumber ε : ℝ)) * (Work.RHPlan.caNumber ε : ℝ)
      = ((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ) := by
    field_simp
  rw [heq] at hmul
  calc ((ArithmeticFunction.sigma 1 (Work.RHPlan.caNumber ε) : ℕ) : ℝ)
      ≤ Real.exp Real.eulerMascheroniConstant
          * Real.log (Real.log (Work.RHPlan.caNumber ε : ℝ)) * (Work.RHPlan.caNumber ε : ℝ) := hmul
    _ = Real.exp Real.eulerMascheroniConstant * (Work.RHPlan.caNumber ε : ℝ)
          * Real.log (Real.log (Work.RHPlan.caNumber ε : ℝ)) := by ring

end

end Work.RHContract
