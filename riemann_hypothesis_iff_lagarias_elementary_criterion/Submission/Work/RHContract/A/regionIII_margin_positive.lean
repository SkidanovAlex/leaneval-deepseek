import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.A.psi_sub_le_of_RH
import Submission.Work.RHContract.A.caXi2_le_sqrt
import Submission.Work.RHContract.A.ca_exp_eq_two_of_between
import Submission.Work.RHContract.A.zeroSumBeta_le
import Submission.Work.RHContract.A.RegionIII.Defs
import Submission.Work.RHContract.A.RegionIII.sum_prime_inv_sq_lower_A2
import Submission.Work.RHContract.A.RegionIII.caC1_lower_regionIII
import Submission.Work.RHContract.A.RegionIII.caNet2_lower_regionIII
import Submission.Work.RHContract.A.RegionIII.caK3_upper_regionIII
import Submission.Work.RHContract.A.RegionIII.caW_upper_regionIII

/-!
# Region III (`ξ = caXi ε ≥ 10^8`): the margin is positive

The margin inequality of `Work.RHContract.A.regionIII_margin_positive`, assembled from the four
explicit bounds proved (or requested) in this neighbourhood, all under the Chebyshev envelope
`|ψ t − t| ≤ 0.45 t^{3/4} + 2` that `Work.RHContract.A.psi_sub_le_of_RH` supplies from `RH`:

* `RegionIII.caC1_lower_regionIII`  : `caC1 ε ≥ (44/100)·u`,
* `RegionIII.caNet2_lower_regionIII`: `caNet2 ε ≥ −(1/200)·u`,
* `RegionIII.caK3_upper_regionIII`  : `caK3 ε ≤ (1/100)·u`,
* `R3.caW_le`                       : `caW ε ≤ (115/1000)·u`

with `u = 1/(√ξ log ξ)`.  Their sum is `(31/100)·u`, while the left-hand side of the margin
inequality is `≤ (27/100)·u` (`β = 2 + γ − log 4π ≤ 48/1000`, `log ξ ≥ 18.42`, `√ξ ≥ 10^4`).
-/

namespace Work.RHContract.A

theorem regionIII_margin_positive (h : RiemannHypothesis) (ε : ℝ) (hε : 0 < ε)
    (hξ : (10 : ℝ) ^ 8 ≤ (Work.RHPlan.caXi ε : ℝ)) :
    ((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi))
        * (5 + 7 / Real.log (Work.RHPlan.caXi ε : ℝ)
            + 4 / (Real.log (Work.RHPlan.caXi ε : ℝ)) ^ 2)
      + Real.log (2 * Real.pi) / Real.sqrt (Work.RHPlan.caXi ε : ℝ)
      + 1 / (Work.RHPlan.caXi ε : ℝ))
    / (Real.sqrt (Work.RHPlan.caXi ε : ℝ) * Real.log (Work.RHPlan.caXi ε : ℝ))
    ≤ Work.RHContract.Margin.caC1 ε + Work.RHContract.Margin.caNet2 ε
        - Work.RHContract.Margin.caW ε - Work.RHContract.Margin.caK3 ε := by
  set ξ : ℝ := (Work.RHPlan.caXi ε : ℝ) with hξdef
  have hξ8 : (10 : ℝ) ^ 8 ≤ ξ := hξ
  have hξpos : 0 < ξ := by nlinarith [hξ8]
  have hξ1 : 1 < ξ := by nlinarith [hξ8]
  -- ### The Chebyshev envelope, from RH
  have hs200 : (200 : ℝ) ≤ Real.sqrt ξ := by
    nlinarith [Real.sq_sqrt hξpos.le, Real.sqrt_nonneg ξ, hξ8]
  have hA2 : ∀ t : ℝ, Real.sqrt ξ ≤ t →
      |Chebyshev.psi t - t| ≤ 0.45 * t ^ (3 / 4 : ℝ) + 2 := by
    intro t ht
    exact Work.RHContract.A.psi_sub_le_of_RH h t (by linarith)
  -- ### The four bounds
  have hC1 : (44 / 100) * RegionIII.caU ξ ≤ Work.RHContract.Margin.caC1 ε :=
    RegionIII.caC1_lower_regionIII ε hε hξ8 hA2
  have hNet2 : -(1 / 200) * RegionIII.caU ξ ≤ Work.RHContract.Margin.caNet2 ε :=
    RegionIII.caNet2_lower_regionIII ε hε hξ8 hA2
  have hK3 : Work.RHContract.Margin.caK3 ε ≤ (1 / 100) * RegionIII.caU ξ :=
    RegionIII.caK3_upper_regionIII ε hε hξ8 hA2
  have hW : Work.RHContract.Margin.caW ε ≤ (12 / 100) * RegionIII.caU ξ :=
    RegionIII.caW_upper_regionIII ε hε hξ8 hA2
  -- ### Numeric helpers
  have hu_pos : 0 < RegionIII.caU ξ := by
    rw [RegionIII.caU]
    exact div_pos (by positivity) (mul_pos (Real.sqrt_pos.mpr hξpos) (Real.log_pos hξ1))
  have hlog10 : (2.30258509 : ℝ) ≤ Real.log 10 := by
    have hmul : Real.log 10 = Real.log 2 + Real.log 5 := by
      rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have h2 : (0.6931471803 : ℝ) ≤ Real.log 2 := Real.log_two_gt_d9.le
    have h5 : (1.6094379123 : ℝ) ≤ Real.log 5 := Real.log_five_gt_d9.le
    linarith
  have hL18 : (18.42 : ℝ) ≤ Real.log ξ := by
    have hpow : Real.log ((10 : ℝ) ^ 8) = 8 * Real.log 10 := by
      rw [Real.log_pow]; norm_num
    have hle : Real.log ((10 : ℝ) ^ 8) ≤ Real.log ξ :=
      Real.log_le_log (by norm_num) hξ8
    rw [hpow] at hle
    linarith
  have hLpos : 0 < Real.log ξ := by linarith
  have hs10k : (10000 : ℝ) ≤ Real.sqrt ξ := by
    have hsqrt : Real.sqrt ((10 : ℝ) ^ 8) = 10000 := by
      rw [show ((10 : ℝ) ^ 8) = (10000 : ℝ) ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)
    calc (10000 : ℝ) = Real.sqrt ((10 : ℝ) ^ 8) := hsqrt.symm
      _ ≤ Real.sqrt ξ := Real.sqrt_le_sqrt hξ8
  -- ### The left-hand side is at most `(27/100) · u ξ`
  have hnum : (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi))
        * (5 + 7 / Real.log ξ + 4 / (Real.log ξ) ^ 2)
      + Real.log (2 * Real.pi) / Real.sqrt ξ + 1 / ξ ≤ 27 / 100 := by
    have hβ0 : 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) ≤ 48 / 1000 :=
      Work.RHContract.A.zeroSumBeta_le
    have h7 : 7 / Real.log ξ ≤ 7 / 18.42 := by
      rw [div_le_div_iff₀ hLpos (by norm_num)]; linarith
    have h4 : 4 / (Real.log ξ) ^ 2 ≤ 4 / (18.42 : ℝ) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have hX0 : (0 : ℝ) ≤ 5 + 7 / Real.log ξ + 4 / (Real.log ξ) ^ 2 := by
      have : 0 ≤ 7 / Real.log ξ := by positivity
      have : 0 ≤ 4 / (Real.log ξ) ^ 2 := by positivity
      linarith
    have hX : 5 + 7 / Real.log ξ + 4 / (Real.log ξ) ^ 2
        ≤ 5 + 7 / 18.42 + 4 / (18.42 : ℝ) ^ 2 := by linarith
    have hlog2pi : Real.log (2 * Real.pi) ≤ 12 := by
      have hpos : 0 < 2 * Real.pi := by positivity
      have h1 := Real.log_le_sub_one_of_pos hpos
      nlinarith [Real.pi_lt_d20]
    have hs2 : Real.log (2 * Real.pi) / Real.sqrt ξ ≤ 12 / 10000 := by
      apply div_le_div₀ (by linarith) hlog2pi (by norm_num) hs10k
    have h1ξ : 1 / ξ ≤ 1 / (10 : ℝ) ^ 8 := by
      rw [div_le_div_iff₀ hξpos (by norm_num)]; linarith
    have hβX : (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi))
        * (5 + 7 / Real.log ξ + 4 / (Real.log ξ) ^ 2)
        ≤ (48 / 1000) * (5 + 7 / 18.42 + 4 / (18.42 : ℝ) ^ 2) := by
      have h1 := mul_le_mul_of_nonneg_right hβ0 hX0
      have h2 : (48 / 1000 : ℝ) * (5 + 7 / Real.log ξ + 4 / (Real.log ξ) ^ 2)
          ≤ (48 / 1000) * (5 + 7 / 18.42 + 4 / (18.42 : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hX (by norm_num)
      linarith
    linarith [hβX, hs2, h1ξ]
  have hLHS : ((2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi))
        * (5 + 7 / Real.log ξ + 4 / (Real.log ξ) ^ 2)
      + Real.log (2 * Real.pi) / Real.sqrt ξ + 1 / ξ) / (Real.sqrt ξ * Real.log ξ)
      ≤ (27 / 100) * RegionIII.caU ξ := by
    have hspos : 0 < Real.sqrt ξ * Real.log ξ :=
      mul_pos (Real.sqrt_pos.mpr hξpos) hLpos
    rw [RegionIII.caU, mul_one_div, div_le_div_iff₀ hspos hspos]
    nlinarith [hnum, hspos]
  -- ### Conclusion
  have hmono : (27 / 100) * RegionIII.caU ξ
      ≤ (Work.RHContract.Margin.caC1 ε + Work.RHContract.Margin.caNet2 ε
          - Work.RHContract.Margin.caW ε - Work.RHContract.Margin.caK3 ε) := by
    linarith [hC1, hNet2, hK3, hW]
  have key := le_trans hLHS hmono
  rw [hξdef] at key
  exact key

end Work.RHContract.A
