import Mathlib
import Submission.Work.RHContract.A.regionII.caNet2_defs

set_option linter.unusedVariables false

namespace Work.RHContract.A.regionII.netGain

/-- **The `c`-bound.**  For `ξ = (caXi ε : ℝ) ∈ [10^5, 10^8)` one has
`netHb ξ + netK (log ξ)/ξ ≤ caC ε`.  This is the analytic input needed by
`netGainBound`: writing `s = √ξ`, `L = log ξ`, it says that the weight `netHb ξ`
which dominates `1/(2p(p−1)log p)` on the gain region plus the gain coefficient
`netK L/s²` still fit below the per-level gain `c = caC ε`.

The proof uses only `ψ ξ ≤ log 3 · ξ` (Hanson's bound), `ψ ξ ≥ (9/10) ξ` and
`log (log 3) ≤ 0.0941`; the remaining content is the explicit rational inequality
`(0.45075 L + 0.125939)/((L + 0.0941)(L/2 + 0.1397)) ≤ (1 − 3/√ξ)/(log 3 ·(L + 0.0941))`,
which reduces to `0.9015 · log 3 ≤ 1 − 3/√ξ` in view of `0.9015 · 0.1397 > 0.125939`. -/
theorem cBound (ε : ℝ) (hε : 0 < ε) (hlo : (100000 : ℝ) ≤ (Work.RHPlan.caXi ε : ℝ))
    (hhi : (Work.RHPlan.caXi ε : ℝ) < (10 : ℝ) ^ 8) :
    netHb (Work.RHPlan.caXi ε : ℝ)
        + netK (Real.log (Work.RHPlan.caXi ε : ℝ)) / (Work.RHPlan.caXi ε : ℝ)
      ≤ Work.RHContract.Margin.caC ε := by
  set ξ : ℝ := (Work.RHPlan.caXi ε : ℝ) with hξdef
  have hξ5 : (100000:ℝ) ≤ ξ := hlo
  have hξ0 : 0 < ξ := by linarith
  have h1530 : (1530:ℝ) ≤ ξ := by linarith
  set L : ℝ := Real.log ξ with hLdef
  have hL0 : 0 < L := by rw [hLdef]; exact Real.log_pos (by linarith)
  have hs316 : (316:ℝ) ≤ Real.sqrt ξ := by
    rw [Real.le_sqrt (by norm_num) (le_of_lt hξ0)]
    nlinarith
  -- Chebyshev bounds on `ψ`
  have hpsi_le : Chebyshev.psi ξ ≤ Real.log 3 * ξ :=
    Commons.NumberTheory.Chebyshev.psi_le_log3_mul_real ξ (le_of_lt hξ0)
  have hpsi_gt : (1:ℝ) < Chebyshev.psi ξ := by
    have h := Commons.NumberTheory.Chebyshev.theta_lower_ninetenths ξ h1530
    have h2 := Chebyshev.theta_le_psi ξ
    linarith
  have hpsi_ge : (1:ℝ) ≤ Chebyshev.psi ξ := le_of_lt hpsi_gt
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  -- the denominator `ψ ξ · log ψ ξ` is dominated by `log 3 · ξ · (L + 0.0941)`
  have hD1 : Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ)
      ≤ (Real.log 3 * ξ) * Real.log (Real.log 3 * ξ) :=
    mul_log_le hpsi_ge hpsi_le
  have hlogln : Real.log (Real.log 3 * ξ) ≤ L + 941/10000 := by
    rw [Real.log_mul (ne_of_gt hlog3pos) (ne_of_gt hξ0), hLdef]
    have := net_log_log3_le
    linarith
  have hD : Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ)
      ≤ (Real.log 3 * ξ) * (L + 941/10000) := by
    refine le_trans hD1 ?_
    exact mul_le_mul_of_nonneg_left hlogln (by positivity)
  have hlogpsi_pos : 0 < Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ) :=
    mul_pos (lt_trans one_pos hpsi_gt) (Real.log_pos hpsi_gt)
  have hnum : 0 ≤ 1 - 3/Real.sqrt ξ := by
    rw [sub_nonneg, div_le_one (Real.sqrt_pos.mpr hξ0)]
    linarith
  have hcaC : Work.RHContract.Margin.caC ε
      = (1 - 3/Real.sqrt ξ)/(Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ)) := by
    rw [Work.RHContract.Margin.caC, ← hξdef]
  -- Step 1: `caC ε` is at least the explicit quotient with `log 3`.
  have hC1 : (1 - 3/Real.sqrt ξ)/((Real.log 3 * ξ) * (L + 941/10000))
      ≤ Work.RHContract.Margin.caC ε := by
    rw [hcaC]
    exact div_le_div_of_nonneg_left hnum hlogpsi_pos hD
  -- Step 2: explicit rational inequality `0.45075 L + 0.125939 ≤ 0.9015 (L/2 + 0.1397)`.
  have hN : (45075:ℝ)/100000 * L + 125939/1000000
      ≤ (9015:ℝ)/10000 * (L/2 + 1397/10000) := by
    have : (0:ℝ) ≤ (9015:ℝ)/10000 * (1397/10000) - 125939/1000000 := by norm_num
    nlinarith
  have hB2pos : 0 < L/2 + 1397/10000 := by linarith
  have hlog3rel : (9015:ℝ)/10000 * Real.log 3 ≤ 1 - 3/Real.sqrt ξ := by
    have h3s : 3/Real.sqrt ξ ≤ 3/316 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs316
    have h1 : (9015:ℝ)/10000 * Real.log 3 ≤ (9015:ℝ)/10000 * 1.0986122888 :=
      mul_le_mul_of_nonneg_left (le_of_lt Real.log_three_lt_d9) (by norm_num)
    have h2 : (9015:ℝ)/10000 * (1.0986122888:ℝ) ≤ 1 - 3/316 := by norm_num
    linarith
  have hB : ((45075:ℝ)/100000 * L + 125939/1000000)/(L/2 + 1397/10000)
      ≤ (1 - 3/Real.sqrt ξ)/Real.log 3 := by
    have h1 : ((45075:ℝ)/100000 * L + 125939/1000000)/(L/2 + 1397/10000)
        ≤ (9015:ℝ)/10000 := by
      rw [div_le_iff₀ hB2pos]; linarith [hN]
    have h2 : (9015:ℝ)/10000 ≤ (1 - 3/Real.sqrt ξ)/Real.log 3 := by
      rw [le_div_iff₀ hlog3pos]; linarith [hlog3rel]
    linarith
  -- Step 3: the `netHb`/`netK` combination equals the displayed quotient.
  have hξA : 0 < ξ * (L + 941/10000) := mul_pos hξ0 (by linarith)
  have hE : netHb ξ + netK L / ξ
      = ((45075:ℝ)/100000 * L + 125939/1000000)
          /(ξ*(L + 941/10000)*(L/2 + 1397/10000)) := by
    have hξne : ξ ≠ 0 := hξ0.ne'
    have hAne : L + 941/10000 ≠ 0 := by linarith
    have hB2ne : L/2 + 1397/10000 ≠ 0 := by linarith
    simp only [netHb, netK, ← hLdef]
    field_simp
    ring
  have hC2 : netHb ξ + netK L / ξ
      ≤ (1 - 3/Real.sqrt ξ)/((Real.log 3 * ξ) * (L + 941/10000)) := by
    rw [hE]
    have ha : ((45075:ℝ)/100000 * L + 125939/1000000)
          /(ξ*(L + 941/10000)*(L/2 + 1397/10000))
        = (((45075:ℝ)/100000 * L + 125939/1000000)/(L/2 + 1397/10000))
          /(ξ*(L + 941/10000)) := by
      rw [div_div]; congr 1; ring
    have hb : (1 - 3/Real.sqrt ξ)/((Real.log 3 * ξ) * (L + 941/10000))
        = ((1 - 3/Real.sqrt ξ)/Real.log 3)/(ξ*(L + 941/10000)) := by
      rw [div_div]; congr 1; ring
    rw [ha, hb]
    exact div_le_div_of_nonneg_right hB (le_of_lt hξA)
  exact le_trans hC2 hC1

end Work.RHContract.A.regionII.netGain
