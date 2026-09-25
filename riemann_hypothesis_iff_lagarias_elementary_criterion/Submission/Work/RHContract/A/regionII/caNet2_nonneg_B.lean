import Mathlib
import Submission.Work.RHContract.A.regionII.Defs
import Submission.Work.RHContract.A.regionII.caNet2_defs
import Submission.Work.RHContract.A.regionII.netMassA
import Submission.Work.RHContract.A.regionII.netMassB
import Submission.Work.RHContract.A.regionII.netMemS
import Submission.Work.RHContract.A.regionII.netLossBound
import Submission.Work.RHContract.A.regionII.netGainBound
import Submission.Work.RHContract.A.regionII.caNet2_arith_A
import Submission.Work.RHContract.A.regionII.caNet2_arith_B
import Submission.Work.RHContract.A.caXi2_le_sqrt
import Submission.Work.RHContract.A.caLevel_le
import Submission.Work.RHContract.A.ca_margin_lower
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.Helper.exp_le_caExp
import Submission.Work.Analysis.Primes.sum_primes_le_third
import Submission.Work.NumberTheory.Chebyshev.theta_deficit_upper
import Submission.Work.RHContract.A.regionII.final_arith2
import Submission.Commons.NumberTheory.Chebyshev.theta_bracket_finite_range
import Submission.Commons.NumberTheory.Chebyshev.psi_sub_theta_eventually_le

/-!
# `caNet2_nonneg_B`: the net gain of the `k = 2` level is nonnegative

For `ξ = ξ(ε) = caXi ε ∈ [10^5, 10^8)` we must show

`Net₂ = ∑_{√ξ < p ≤ ξ₂} (c·log p − 1/(2p(p−1))) ≥ 0`,  `c = caC ε = (1−3/√ξ)/(ψ ξ · log ψ ξ)`.

The summands of `Net₂` are *not* individually nonnegative: at `p ≈ √ξ` the term
`c log p − 1/(2p(p−1))` is slightly negative (by about `1.5·10^-7/ξ`).  The gain comes from the
much larger number of primes further up the interval, so both the negative boundary part and the
positive bulk have to be controlled quantitatively.

* The bulk `∑_{P<p≤ξ₂} log p = θ(ξ₂) − θ(P)`, `P = (115/100)√ξ`, is bounded below by
  `(ξ₂ − 2.3√ξ₂) − (P − (1/2)√P)`: the first bracket is the hypothesis `hθ`, the second is the
  *certified* deficit bound `theta_deficit_half` (`θ t ≤ t − (1/2)√t` on `[360,12000]`), proved
  below by a finite check against the Chebyshev table `CU` of
  `Commons.NumberTheory.Chebyshev.theta_bracket_finite_range`.
* The boundary `∑_{√ξ<p≤P}(h(p) − c)^+ log p`, `h(p) = 1/(2p(p−1)log p)`, is bounded above by
  the elementary Cauchy–Schwarz-type bound
  `(1/3)·log P·max_{y ∈ [c₀,c₁]} (√(A/(m−1)) − √(y(m−1)))²`, `A = 1/(2 log(m+1))`,
  where the factor `1/3` uses that primes `> 3` lie in two of every six residue classes mod 6.
* The two explicit bounds `c₀ ≤ c ≤ c₁` for `c` come from `ψ ξ ≤ log 3 · ξ` (Hanson) and
  `θ ξ ≥ (9/10) ξ` (Chebyshev's bound).

The whole inequality is finally a fully explicit inequality in `ξ ∈ [10^5, 10^8)`.
-/

open scoped BigOperators
open Commons.NumberTheory.Chebyshev Commons.NumberTheory.Chebyshev.ThetaBracket

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Work.RHContract.A.regionII

noncomputable section

theorem caNet2_nonneg_B (ε : ℝ) (hε : 0 < ε)
    (hlo : 100000 ≤ (Work.RHPlan.caXi ε : ℝ)) (hhi : (Work.RHPlan.caXi ε : ℝ) < (10:ℝ)^8)
    (hθ : ∀ t : ℝ, 173 ≤ t → t ≤ 100000 → t - Chebyshev.theta t ≤ 2.3 * Real.sqrt t) :
    0 ≤ Work.RHContract.Margin.caNet2 ε := by
  -- ============ 0. setup ============
  set ξ : ℝ := (Work.RHPlan.caXi ε : ℝ) with hξdef
  have hξ0 : 0 < ξ := by linarith
  have hξ1530 : (1530 : ℝ) ≤ ξ := by linarith
  have hξ1e5 : (100000 : ℝ) ≤ ξ := hlo
  have hξ1e8 : ξ < (10:ℝ)^8 := hhi
  set s : ℝ := Real.sqrt ξ with hsdef
  have hs0 : 0 < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hξ0
  have hs316 : (316 : ℝ) ≤ s := by
    have h1 : (316:ℝ) ≤ Real.sqrt 100000 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have h2 : Real.sqrt 100000 ≤ s := by rw [hsdef]; exact Real.sqrt_le_sqrt hξ1e5
    linarith
  have hsmin : (316.2 : ℝ) ≤ s := by
    have h1 : (316.2:ℝ) ≤ Real.sqrt 100000 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
    have h2 : Real.sqrt 100000 ≤ s := by rw [hsdef]; exact Real.sqrt_le_sqrt hξ1e5
    linarith
  have hs1e4 : s ≤ (10000:ℝ) := by
    rw [hsdef, Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    push_cast; linarith
  have hs2 : s^2 = ξ := by rw [hsdef]; exact Real.sq_sqrt hξ0.le
  set L : ℝ := Real.log ξ with hLdef
  have hlogs : Real.log s = L/2 := by rw [hsdef, Real.log_sqrt hξ0.le, hLdef]
  have hexpL : Real.exp (L/2) = s := by rw [← hlogs, Real.exp_log hs0]
  have hlog10lo : (2.3025850926:ℝ) ≤ Real.log 10 := by
    have h : Real.log (10:ℝ) = Real.log 2 + Real.log 5 := by
      rw [show (10:ℝ) = 2*5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hlog10hi : Real.log (10:ℝ) ≤ 2.3025850940 := by
    have h : Real.log (10:ℝ) = Real.log 2 + Real.log 5 := by
      rw [show (10:ℝ) = 2*5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hL115 : (11.5:ℝ) ≤ L := by
    rw [hLdef]
    have h1 : Real.log (100000:ℝ) ≤ Real.log ξ := Real.log_le_log (by norm_num) hξ1e5
    have h2 : Real.log (100000:ℝ) = 5 * Real.log 10 := by
      rw [show (100000:ℝ) = 10^5 by norm_num, Real.log_pow]; norm_num
    linarith
  have hL19 : L ≤ 19 := by
    rw [hLdef]
    have h1 : Real.log ξ < Real.log ((10:ℝ)^8) := Real.log_lt_log hξ0 hξ1e8
    have h2 : Real.log ((10:ℝ)^8) = 8 * Real.log 10 := by
      rw [Real.log_pow]; norm_num
    linarith
  -- ============ 1. bounds on c = caC ε ============
  have hcaC : Work.RHContract.Margin.caC ε
      = (1 - 3/s)/(Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ)) := by
    rw [Work.RHContract.Margin.caC, ← hξdef, ← hsdef]
  have hpsi_le : Chebyshev.psi ξ ≤ Real.log 3 * ξ :=
    Commons.NumberTheory.Chebyshev.psi_le_log3_mul_real ξ (le_of_lt hξ0)
  have hpsi_ge : (9/10:ℝ) * ξ ≤ Chebyshev.psi ξ :=
    le_trans (Commons.NumberTheory.Chebyshev.theta_lower_ninetenths ξ hξ1530)
      (Chebyshev.theta_le_psi ξ)
  have hpsi1 : (1:ℝ) ≤ Chebyshev.psi ξ := by linarith
  have hnum0 : 0 ≤ 1 - 3/s := by
    have h3 : 3/s ≤ 3/316 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs316
    linarith
  have hlog31 : (1:ℝ) ≤ Real.log 3 * ξ := by
    have := log_three_gt_one
    nlinarith [hξ1e5]
  have hlogpsi : 0 < Real.log (Chebyshev.psi ξ) := Real.log_pos (by linarith)
  have hlog95 : 0 < Real.log ((9/10) * ξ) := Real.log_pos (by linarith)
  have hc_low : (1 - 3/s)/(Real.log 3 * ξ * Real.log (Real.log 3 * ξ))
      ≤ Work.RHContract.Margin.caC ε := by
    rw [hcaC]
    have hpos : 0 < Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ) := mul_pos (by linarith) hlogpsi
    have hle : Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ)
        ≤ Real.log 3 * ξ * Real.log (Real.log 3 * ξ) := mul_log_le hpsi1 hpsi_le
    calc (1 - 3/s)/(Real.log 3 * ξ * Real.log (Real.log 3 * ξ))
        = (1 - 3/s)/(Real.log 3 * ξ * Real.log (Real.log 3 * ξ)) := rfl
      _ ≤ (1 - 3/s)/(Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ)) :=
          div_le_div_of_nonneg_left hnum0 hpos hle
  have hc_up : Work.RHContract.Margin.caC ε
      ≤ (1 - 3/s)/((9/10) * ξ * Real.log ((9/10) * ξ)) := by
    rw [hcaC]
    have hpos : 0 < (9/10:ℝ) * ξ * Real.log ((9/10) * ξ) := by positivity
    have hle : (9/10:ℝ) * ξ * Real.log ((9/10) * ξ) ≤ Chebyshev.psi ξ * Real.log (Chebyshev.psi ξ) :=
      mul_log_le (by linarith) hpsi_ge
    exact div_le_div_of_nonneg_left hnum0 hpos hle
  have hc0 : 0 < Work.RHContract.Margin.caC ε := by
    have h : 0 < (1 - 3/s)/(Real.log 3 * ξ * Real.log (Real.log 3 * ξ)) := by
      apply div_pos
      · have : 3/s ≤ 3/316 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs316
        linarith
      · have hpos2 : 0 < Real.log (Real.log 3 * ξ) := Real.log_pos (by linarith)
        nlinarith [hlog31, hpos2]
    linarith [hc_low]
  classical
  -- ============ 2. the net gain of the two regions ============
  have hL1845 : L ≤ (1845/100 : ℝ) := by
    have h1 : Real.log ξ < Real.log ((10:ℝ)^8) := Real.log_lt_log hξ0 hξ1e8
    have h2 : Real.log ((10:ℝ)^8) = 8 * Real.log 10 := by rw [Real.log_pow]; norm_num
    rw [hLdef]
    linarith
  have hb115 : ((115:ℝ)/10) ≤ L := by linarith
  have hnet2 : Work.RHContract.Margin.caNet2 ε
      = ∑ p ∈ netS ε, netF (Work.RHContract.Margin.caC ε) p := by
    unfold Work.RHContract.Margin.caNet2 netS netF netM
    rfl
  have hs4pos : 0 < s - 4 := by linarith
  have hloss := netLossBound ε hε hlo hhi
  have hloss' : -(netY L / (s - 4))
      ≤ ∑ p ∈ (netS ε).filter (fun q => q ≤ netPf ξ), netF (Work.RHContract.Margin.caC ε) p := by
    simpa only [← hξdef, ← hsdef, ← hLdef] using hloss
  have hgain := netGainBound ε hε hlo hhi
    (fun p hp h1 h2 => netMemS ε hε hlo hhi p hp h1 h2)
  have hgain' : netK L / s ^ 2 * netMasslb s L
      ≤ ∑ p ∈ (netS ε).filter (fun q => ¬ q ≤ netPf ξ), netF (Work.RHContract.Margin.caC ε) p := by
    have h1 : (netS ε).filter (fun q => netPf ξ < q)
        = (netS ε).filter (fun q => ¬ q ≤ netPf ξ) := by
      apply Finset.filter_congr
      intro q _
      exact ⟨fun h => not_le.mpr h, fun h => lt_of_not_ge h⟩
    rw [← h1]
    simpa only [← hξdef, ← hsdef, ← hLdef] using hgain
  have hnu : (if s ≤ 1000 then netNuA L else netNuB L) ≤ netMasslb s L * (s - 4) / s ^ 2 := by
    by_cases h : s ≤ 1000
    · rw [if_pos h]; exact netMassA s L hsmin hL115
    · rw [if_neg h]; exact netMassB s L (le_of_lt (not_le.mp h)) hL115
  have hL2 : L = 2 * Real.log s := by
    rw [hLdef, ← hs2, Real.log_pow]
    norm_num
  have harith : netY L ≤ netK L * (if s ≤ 1000 then netNuA L else netNuB L) := by
    by_cases h : s ≤ 1000
    · rw [if_pos h]
      have hLm : L ≤ 13.8156 := by
        have h1 : Real.log s ≤ Real.log 1000 := Real.log_le_log (by linarith) h
        have h1000 : Real.log (1000 : ℝ) = 3 * Real.log 10 := by
          rw [show (1000 : ℝ) = 10 ^ 3 by norm_num, Real.log_pow]; norm_num
        have h2 : 2 * Real.log s ≤ 2 * (3 * Real.log 10) := by rw [← h1000]; linarith
        rw [hL2]
        linarith
      exact caNet2_arith_A L hb115 hLm
    · rw [if_neg h]
      have hLm : (138155/10000 : ℝ) ≤ L := by
        have h1 : Real.log 1000 ≤ Real.log s := Real.log_le_log (by norm_num) (le_of_lt (not_le.mp h))
        have h1000 : Real.log (1000 : ℝ) = 3 * Real.log 10 := by
          rw [show (1000 : ℝ) = 10 ^ 3 by norm_num, Real.log_pow]; norm_num
        have h2 : 2 * (3 * Real.log 10) ≤ 2 * Real.log s := by rw [← h1000]; linarith
        rw [hL2]
        linarith
      exact caNet2_arith_B L hLm hL1845
  have hKpos : 0 < netK L := by
    rw [netK]
    apply div_pos
    · nlinarith [hL115]
    · apply mul_pos <;> nlinarith [hL115]
  have hgain5 : netK L * (if s ≤ 1000 then netNuA L else netNuB L) / (s - 4)
      ≤ netK L / s ^ 2 * netMasslb s L := by
    rw [div_le_iff₀ hs4pos]
    have h : netK L / s ^ 2 * netMasslb s L * (s - 4)
        = netK L * (netMasslb s L * (s - 4) / s ^ 2) := by
      field_simp
      try ring
    rw [h]
    exact mul_le_mul_of_nonneg_left hnu (le_of_lt hKpos)
  have hfin : 0 ≤ -(netY L / (s - 4))
      + netK L * (if s ≤ 1000 then netNuA L else netNuB L) / (s - 4) := by
    have h : -(netY L / (s - 4)) + netK L * (if s ≤ 1000 then netNuA L else netNuB L) / (s - 4)
        = (netK L * (if s ≤ 1000 then netNuA L else netNuB L) - netY L) / (s - 4) := by ring
    rw [h]
    apply div_nonneg _ (le_of_lt hs4pos)
    linarith [harith]
  rw [hnet2]
  rw [← Finset.sum_filter_add_sum_filter_not (netS ε) (fun q => q ≤ netPf ξ)
    (fun q => netF (Work.RHContract.Margin.caC ε) q)]
  linarith [hloss', hgain', hgain5, hfin]





end

end Work.RHContract.A.regionII
