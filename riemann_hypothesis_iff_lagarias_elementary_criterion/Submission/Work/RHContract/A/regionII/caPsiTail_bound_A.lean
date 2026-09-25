import Mathlib
import Submission.Work.RHContract.A.regionII.Defs
import Submission.Work.RHContract.A.psiTail_ge_of_RH
import Submission.Work.RHContract.A.zeroSumBeta_le

/-!
# Region II (`30000 ≤ ξ < 10^5`): the lower bound for `J = psiTail`

Under `RH` and for `ξ ≥ 1000` one has (`Work.RHContract.A.psiTail_ge_of_RH`)

`psiTail ξ ≥ −caCJ ξ · caU ξ`,   `caU ξ = 1/(√ξ log ξ)`,

with `caCJ ξ = β(5 + 7/L + 4/L²) + log(2π)/√ξ + 1/ξ`, `β = 2 + γ − log 4π`, `L = log ξ`.

Here we show that on the range `ξ ≥ 30000` of Region II the constant `caCJ ξ` is at
most `287/1000`, which gives the stated bound `psiTail ξ ≥ −(287/1000)·caU ξ`.

The numerical estimates used are:

* `β ≤ 48/1000` (`Work.RHContract.A.zeroSumBeta_le`);
* `log 30000 ≥ 10.3`, hence `7/log ξ + 4/log²ξ ≤ 70/103 + 400/10609`;
* `log(2π) ≤ 2` and `√ξ ≥ 173`;
* `1/ξ ≤ 1/30000`,

so that the right-hand side is at most
`(48/1000)(5 + 70/103 + 400/10609) + 2/173 + 1/30000 ≤ 287/1000`.
-/

namespace Work.RHContract.A.regionII

/-- `log 30000 ≥ 10.3`, from the decimal bounds on `log 2`, `log 3`, `log 5`. -/
private lemma log_30000_ge : (10.3 : ℝ) ≤ Real.log 30000 := by
  have h : Real.log 30000 = Real.log 3 + 4 * Real.log 10 := by
    rw [show (30000 : ℝ) = 3 * 10 ^ 4 by norm_num, Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
    norm_num
  have h10 : Real.log 10 = Real.log 2 + Real.log 5 := Real.log_ten_eq
  have h2 := Real.log_two_gt_d9
  have h5 := Real.log_five_gt_d9
  have h3 := Real.log_three_gt_d9
  rw [h, h10]
  linarith

/-- `log (2π) ≤ 2`. -/
private lemma log_two_pi_le_two : Real.log (2 * Real.pi) ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by positivity : (0:ℝ) < 2 * Real.pi)]
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
  rw [h2]
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hp : 2 * Real.pi < 6.29 := by nlinarith [Real.pi_lt_d20]
  nlinarith [he, hp, Real.exp_pos 1]

/-- `caU ξ > 0` for `ξ ≥ 30000`. -/
private lemma caU_pos {ξ : ℝ} (hξ : 30000 ≤ ξ) : 0 < RegionII.caU ξ := by
  have hξpos : (0:ℝ) < ξ := by linarith
  have hL : (0:ℝ) < Real.log ξ := by
    have h1 : (10.3:ℝ) ≤ Real.log ξ := le_trans log_30000_ge (Real.log_le_log (by norm_num) hξ)
    linarith
  rw [RegionII.caU]
  positivity

/-- The constant bound of Region II: `caCJ ξ ≤ 287/1000` for `ξ ≥ 30000`. -/
private lemma caCJ_le_of (ξ : ℝ) (hξ : 30000 ≤ ξ) : RegionII.caCJ ξ ≤ 287/1000 := by
  have hξpos : (0:ℝ) < ξ := by linarith
  have hL : (10.3:ℝ) ≤ Real.log ξ := le_trans log_30000_ge (Real.log_le_log (by norm_num) hξ)
  have hLpos : (0:ℝ) < Real.log ξ := by linarith
  have hβ : 2 + Real.eulerMascheroniConstant - Real.log (4*Real.pi) ≤ 48/1000 :=
    Work.RHContract.A.zeroSumBeta_le
  have hlog2pi : Real.log (2*Real.pi) ≤ 2 := log_two_pi_le_two
  have hsqrt : (173:ℝ) ≤ Real.sqrt ξ := by
    rw [Real.le_sqrt (by norm_num) (le_of_lt hξpos)]
    norm_num
    linarith
  have hq : 5 + 7/Real.log ξ + 4/(Real.log ξ)^2 ≤ 5 + 70/103 + 400/10609 := by
    have h1 : 7/Real.log ξ ≤ 70/103 := by
      have h := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 7 by norm_num)
        (show (0:ℝ) < (10.3:ℝ) by norm_num) hL
      have he : 7/(10.3:ℝ) = 70/103 := by norm_num
      linarith [h, he]
    have h2 : 4/(Real.log ξ)^2 ≤ 400/10609 := by
      have hsq : ((10.3:ℝ))^2 ≤ (Real.log ξ)^2 := by nlinarith
      have h := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 4 by norm_num)
        (show (0:ℝ) < (10.3:ℝ)^2 by norm_num) hsq
      have he : 4 / ((10.3:ℝ)^2) = 400/10609 := by norm_num
      linarith [h, he]
    linarith
  have hc0 : 0 ≤ 5 + 7/Real.log ξ + 4/(Real.log ξ)^2 := by
    have ha : 0 ≤ 7/Real.log ξ := div_nonneg (by norm_num) hLpos.le
    have hb : 0 ≤ 4/(Real.log ξ)^2 := div_nonneg (by norm_num) (pow_pos hLpos 2).le
    linarith
  have hterm : (2 + Real.eulerMascheroniConstant - Real.log (4*Real.pi))
        * (5 + 7/Real.log ξ + 4/(Real.log ξ)^2)
      ≤ (48/1000) * (5 + 70/103 + 400/10609) := mul_le_mul hβ hq hc0 (by norm_num)
  have h2pi : Real.log (2*Real.pi)/Real.sqrt ξ ≤ 2/173 := by
    have h1 : Real.log (2*Real.pi)/Real.sqrt ξ ≤ 2/Real.sqrt ξ :=
      div_le_div_of_nonneg_right hlog2pi (Real.sqrt_nonneg ξ)
    have h2 : 2/Real.sqrt ξ ≤ 2/173 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsqrt
    linarith
  have hinv : 1/ξ ≤ 1/30000 := one_div_le_one_div_of_le (by norm_num) hξ
  have hnum : (48/1000) * (5 + 70/103 + 400/10609) + 2/173 + 1/30000 ≤ 287/1000 := by norm_num
  rw [RegionII.caCJ]
  linarith

theorem caPsiTail_bound_A (h : RiemannHypothesis) (ε : ℝ) (hε : 0 < ε)
    (hlo : 30000 ≤ (Work.RHPlan.caXi ε : ℝ)) (hhi : (Work.RHPlan.caXi ε : ℝ) < 100000) :
    -(287/1000) * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ)
      ≤ Work.RHContract.psiTail (Work.RHPlan.caXi ε : ℝ) := by
  have hx : (1000:ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) := by linarith
  have h1 := Work.RHContract.A.psiTail_ge_of_RH h (Work.RHPlan.caXi ε : ℝ) hx
  have hneg : -((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi))
        * (5 + 7 / Real.log (Work.RHPlan.caXi ε : ℝ) + 4 / (Real.log (Work.RHPlan.caXi ε : ℝ)) ^ 2)
      + Real.log (2 * Real.pi) / Real.sqrt (Work.RHPlan.caXi ε : ℝ) + 1 / (Work.RHPlan.caXi ε : ℝ))
      / (Real.sqrt (Work.RHPlan.caXi ε : ℝ) * Real.log (Work.RHPlan.caXi ε : ℝ))
      = -Work.RHContract.A.RegionII.caCJ (Work.RHPlan.caXi ε : ℝ)
        * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ) := by
    rw [Work.RHContract.A.RegionII.caCJ, Work.RHContract.A.RegionII.caU]
    ring
  have hmain : -Work.RHContract.A.RegionII.caCJ (Work.RHPlan.caXi ε : ℝ)
      * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ)
      ≤ Work.RHContract.psiTail (Work.RHPlan.caXi ε : ℝ) := by
    rw [← hneg]
    exact h1
  have hcJ := caCJ_le_of (Work.RHPlan.caXi ε : ℝ) hlo
  have hu : 0 ≤ Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ) :=
    le_of_lt (caU_pos hlo)
  have hstep : -(287/1000) * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ)
      ≤ -Work.RHContract.A.RegionII.caCJ (Work.RHPlan.caXi ε : ℝ)
        * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hcJ hu
    have e1 : -(287/1000) * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ)
        = -((287/1000) * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ)) := by ring
    have e2 : -Work.RHContract.A.RegionII.caCJ (Work.RHPlan.caXi ε : ℝ)
        * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ)
        = -(Work.RHContract.A.RegionII.caCJ (Work.RHPlan.caXi ε : ℝ)
        * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ)) := by ring
    rw [e1, e2]
    linarith
  exact le_trans hstep hmain

end Work.RHContract.A.regionII
