import Mathlib
import Submission.Work.RHContract.A.regionII.Defs
import Submission.Work.RHContract.A.psiTail_ge_of_RH
import Submission.Work.RHContract.A.zeroSumBeta_le

/-!
# Region II (`10^5 ≤ ξ(ε) < 10^8`): the lower bound for `J = psiTail`

`Work.RHContract.A.psiTail_ge_of_RH` (AREA A1) gives, under `RH`, for every `x ≥ 1000`,

  `J(x) = psiTail x ≥ −c(x)·u(x)`,  `u(x) = 1/(√x log x)`,
  `c(x) = β·(5 + 7/log x + 4/log²x) + log(2π)/√x + 1/x`,  `β = 2 + γ − log 4π`.

On the range `ξ ≥ 10^5` the constant `c(ξ)` is below `28/100`: the numerical inputs are

* `β ≤ 48/1000` (`Work.RHContract.A.zeroSumBeta_le`, unconditional),
* `log ξ ≥ 11.5` (from `ξ ≥ 10^5` and `log 10 ≥ 2.3025850926`, i.e. the Mathlib decimals
  `Real.log_two_gt_d9`, `Real.log_five_gt_d9`),
* `√ξ ≥ 316` (from `ξ ≥ 10^5`),
* `log (2π) ≤ 2` (from `2π < e²` and `Real.exp_one_gt_d9`, `Real.pi_lt_d20`).

Indeed `48/1000·(5 + 7/11.5 + 4/11.5²) + 2/316 + 1/10^5 < 28/100`.
-/

namespace Work.RHContract.A.regionII

/-- `log 10 ≥ 2.3025850926`, from the Mathlib decimals for `log 2` and `log 5`. -/
private lemma log_ten_lower : (2.3025850926 : ℝ) ≤ Real.log 10 := by
  have h : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h5 : (1.6094379123 : ℝ) < Real.log 5 := Real.log_five_gt_d9
  linarith

/-- `log (2π) ≤ 2`, since `2π < 6.284 < e²` and `e > 2.7182818283`. -/
private lemma log_two_pi_le_two : Real.log (2 * Real.pi) ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by positivity)]
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he2 : Real.exp 2 = (Real.exp 1) ^ 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    ring
  rw [he2]
  have hsq : (2.7182818283 : ℝ) ^ 2 < (Real.exp 1) ^ 2 := by
    nlinarith [h1, Real.exp_pos 1]
  have hpi : 2 * Real.pi < 6.28318530717958647694 := by linarith [Real.pi_lt_d20]
  nlinarith [hsq, hpi]

/-- **Region II, range `10^5 ≤ ξ(ε) < 10^8`**: under `RH`,
`psiTail ξ ≥ −(28/100)·u(ξ)` with `u(ξ) = 1/(√ξ log ξ)`.

Immediate from AREA A1 `psiTail_ge_of_RH` together with the numerical bound `c(ξ) ≤ 28/100`
valid on the range (see the module docstring). -/
theorem caPsiTail_bound_B (h : RiemannHypothesis) (ε : ℝ) (hε : 0 < ε)
    (hlo : 100000 ≤ (Work.RHPlan.caXi ε : ℝ)) (hhi : (Work.RHPlan.caXi ε : ℝ) < (10:ℝ)^8) :
    -(28/100) * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ)
      ≤ Work.RHContract.psiTail (Work.RHPlan.caXi ε : ℝ) := by
  set x : ℝ := (Work.RHPlan.caXi ε : ℝ) with hxdef
  have hx1e5 : (100000 : ℝ) ≤ x := by simpa [hxdef] using hlo
  have hx1000 : (1000 : ℝ) ≤ x := by linarith
  have hx0 : (0:ℝ) < x := by linarith
  have hx1 : (1:ℝ) < x := by linarith
  have hL0 : 0 < Real.log x := Real.log_pos hx1
  have hS0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hden : 0 < Real.sqrt x * Real.log x := mul_pos hS0 hL0
  -- `log ξ ≥ 11.5`
  have hlogx : (11.5 : ℝ) ≤ Real.log x := by
    have h1e5pos : (0:ℝ) < 100000 := by norm_num
    have hle : Real.log (100000:ℝ) ≤ Real.log x := Real.log_le_log h1e5pos hx1e5
    have h100 : Real.log (100000:ℝ) = 5 * Real.log 10 := by
      rw [show (100000:ℝ) = 10^5 by norm_num, Real.log_pow]
      norm_num
    have h10 : (2.3025850926:ℝ) ≤ Real.log 10 := log_ten_lower
    linarith
  -- `√ξ ≥ 316`
  have hsqrt316 : (316:ℝ) ≤ Real.sqrt x := by
    have h1 : Real.sqrt (100000:ℝ) ≤ Real.sqrt x := Real.sqrt_le_sqrt hx1e5
    have h2 : (316:ℝ) ≤ Real.sqrt (100000:ℝ) := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    linarith
  -- the numerical constant of A1
  have hA : 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) ≤ 48/1000 :=
    Work.RHContract.A.zeroSumBeta_le
  have hc1 : 7 / Real.log x ≤ 7 / 11.5 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlogx
  have hc2 : 4 / (Real.log x)^2 ≤ 4 / (11.5:ℝ)^2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 11.5) hlogx 2)
  have hc0 : 0 ≤ 5 + 7/Real.log x + 4/(Real.log x)^2 := by
    have ha : 0 ≤ 7 / Real.log x := div_nonneg (by norm_num) hL0.le
    have hb : 0 ≤ 4 / (Real.log x)^2 := div_nonneg (by norm_num) (pow_pos hL0 2).le
    linarith
  have hprod : (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi))
        * (5 + 7 / Real.log x + 4 / (Real.log x) ^ 2)
      ≤ (48/1000) * (5 + 7/11.5 + 4/(11.5:ℝ)^2) := by
    refine mul_le_mul hA ?_ hc0 (by norm_num)
    linarith
  have hlog2pi : Real.log (2 * Real.pi) ≤ 2 := log_two_pi_le_two
  have hlog2pi0 : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hterm1 : Real.log (2 * Real.pi) / Real.sqrt x ≤ 2/316 := by
    have h1 : Real.log (2 * Real.pi) / Real.sqrt x ≤ Real.log (2 * Real.pi) / 316 :=
      div_le_div_of_nonneg_left hlog2pi0 (by norm_num) hsqrt316
    have h2 : Real.log (2 * Real.pi) / 316 ≤ 2/316 :=
      div_le_div_of_nonneg_right hlog2pi (by norm_num)
    linarith
  have hterm2 : 1/x ≤ 1/100000 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx1e5
  have hB : (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi))
        * (5 + 7 / Real.log x + 4 / (Real.log x) ^ 2)
      + Real.log (2 * Real.pi) / Real.sqrt x + 1 / x ≤ 28/100 := by
    have hnum : (48/1000) * (5 + 7/11.5 + 4/(11.5:ℝ)^2) + 2/316 + 1/100000 < 28/100 := by
      norm_num
    linarith [hprod, hterm1, hterm2, hnum]
  -- AREA A1
  have hpsi := Work.RHContract.A.psiTail_ge_of_RH h x hx1000
  have hkey : -(28/100) / (Real.sqrt x * Real.log x)
      ≤ (-((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi))
          * (5 + 7 / Real.log x + 4 / (Real.log x) ^ 2)
        + Real.log (2 * Real.pi) / Real.sqrt x + 1 / x)) / (Real.sqrt x * Real.log x) := by
    apply div_le_div_of_nonneg_right _ hden.le
    linarith
  have hgoal : -(28/100) * Work.RHContract.A.RegionII.caU x
      = -(28/100)/(Real.sqrt x * Real.log x) := by
    rw [Work.RHContract.A.RegionII.caU]
    ring
  rw [hgoal]
  linarith [hkey, hpsi]

end Work.RHContract.A.regionII
