import Mathlib
import Submission.ChenPlan.Interfaces
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiEnvDefs
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiEnvBasic
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiEnv_integral
import Submission.Work.NumberTheory.Chen.APSwitchUpper.Aprime_four_ge_sharp
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhi_le_env
import Submission.Work.NumberTheory.Chen.BTermCount.riUp_eq_twoExpGamma_div
import Submission.Work.NumberTheory.Chen.ApSumTenth.twoExpGamma_ge_seven_halves

open MeasureTheory
open Work.NumberTheory.Chen.APSwitchUpper

namespace Work.ChenPlan.LinearSieve.Numerics

noncomputable section

set_option maxHeartbeats 1000000

/-! ## §1  A midpoint lower bound for `Aprime` -/

/-- The rational lower bound `fLow` for the integrand of `Aprime`. -/
private theorem fLow_le_integrand (v : ℝ) (hv : 2 ≤ v) (hv4 : v ≤ 4) :
    fLow v ≤ Real.log (3 / (v - 1)) / v := by
  have hv0 : (0 : ℝ) < v := by linarith
  have h3 : 3 / (v - 1) ∈ Set.Icc 1 3 := by
    rw [Set.mem_Icc]
    exact ⟨by rw [le_div_iff₀ (by linarith : (0 : ℝ) < v - 1)]; linarith,
      by rw [div_le_iff₀ (by linarith : (0 : ℝ) < v - 1)]; linarith⟩
  rw [show fLow v = logLowRat (3 / (v - 1)) / v from rfl]
  exact div_le_div_of_nonneg_right (logLowRat_le h3.1) hv0.le

private lemma continuousOn_integrand {a b : ℝ} (ha : 2 ≤ a) (hb : b ≤ 4) :
    ContinuousOn (fun v : ℝ => Real.log (3 / (v - 1)) / v) (Set.Icc a b) := by
  refine ContinuousOn.div ?_ continuousOn_id (fun v hv => by
    rw [Set.mem_Icc] at hv; linarith [hv.1, ha])
  refine ContinuousOn.log ?_ (fun v hv => ?_)
  · exact ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
      (fun v hv => by rw [Set.mem_Icc] at hv; linarith [hv.1, ha])
  · rw [Set.mem_Icc] at hv
    exact ne_of_gt (div_pos (by norm_num) (by linarith [hv.1, ha]))

/-- **Midpoint (one-step) lower bound for `Aprime`.**  If `Am ≤ Aprime a` and `2 ≤ a ≤ x ≤ 4`,
then `Am + (x - a)·fLow ((a+x)/2) ≤ Aprime x`: the integrand `log (3/(v-1))/v` is convex on
`[2,4]`, so the midpoint rule underestimates its integral. -/
private theorem Abnd_le_Aprime {a Am x : ℝ} (ha : 2 ≤ a) (hax : a ≤ x) (hx4 : x ≤ 4)
    (hAm : Am ≤ Aprime a) :
    Am + (x - a) * fLow ((a + x) / 2) ≤ Aprime x := by
  have hxa : (2 : ℝ) ≤ x := le_trans ha hax
  have hconv : ConvexOn ℝ (Set.Icc a x) (fun v : ℝ => Real.log (3 / (v - 1)) / v) :=
    convexOn_aprimeIntegrand.subset (fun v hv => by
      rw [Set.mem_Icc] at hv ⊢
      exact ⟨le_trans ha hv.1, le_trans hv.2 hx4⟩) (convex_Icc a x)
  have hint : IntervalIntegrable (fun v : ℝ => Real.log (3 / (v - 1)) / v) volume a x :=
    ContinuousOn.intervalIntegrable_of_Icc hax (continuousOn_integrand ha hx4)
  have hmid := midpoint_integral_le hax (midpoint_jensen_of_convexOn hconv) hint
  have hlow : (x - a) * fLow ((a + x) / 2)
      ≤ (x - a) * (Real.log (3 / ((a + x) / 2 - 1)) / ((a + x) / 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    exact fLow_le_integrand ((a + x) / 2) (by linarith) (by linarith)
  have hsub := Aprime_sub_eq ha hax
  have hmono := Aprime_monoOn ⟨ha, le_trans hax hx4⟩ ⟨hxa, hx4⟩ hax
  linarith [hmid, hlow, hsub, hmono, hAm]

/-! ## §2  The numerical bound `2e^γ ≤ 3.578` -/

/-- `γ < 5812/10000`, from the decreasing sequence `H_n - log n` at `n = 128`. -/
private theorem eulerMascheroniConstant_lt_5812 :
    Real.eulerMascheroniConstant < (5812 : ℝ) / 10000 := by
  have hseq : Real.eulerMascheroniSeq' 128 = (harmonic 128 : ℝ) - Real.log 128 := by
    rw [Real.eulerMascheroniSeq']; norm_num
  have h1 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 128
  rw [hseq] at h1
  have hH : (harmonic 128 : ℝ) ≤ 5433148 / 1000000 := by norm_num [harmonic]
  have hlog : (4852030 : ℝ) / 1000000 ≤ Real.log 128 := by
    have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have hp : Real.log 128 = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
      norm_num
    rw [hp]; linarith
  linarith

/-- `exp (5812/10000) ≤ 1789/1000`. -/
private theorem exp_5812_le : Real.exp ((5812 : ℝ) / 10000) ≤ (1789 : ℝ) / 1000 := by
  have h := Real.exp_bound' (x := (5812 : ℝ) / 10000) (by norm_num) (by norm_num)
    (n := 5) (by norm_num)
  norm_num at h
  linarith

/-- `2e^γ ≤ 3.578`. -/
private theorem twoExpGamma_le_3578 :
    2 * Real.exp Real.eulerMascheroniConstant ≤ (3578 : ℝ) / 1000 := by
  have hmono : Real.exp Real.eulerMascheroniConstant < Real.exp ((5812 : ℝ) / 10000) :=
    Real.exp_lt_exp.mpr eulerMascheroniConstant_lt_5812
  have hexp := exp_5812_le
  linarith

/-! ## §3  Rational bounds for `ALow` at the grid points `2, 5/2, 3, 7/2` -/

private theorem ALow_zero_ge : (0 : ℝ) ≤ ALow 0 := by
  simp [ALow]

private theorem ALow_eight_ge : (19846 / 100000 : ℝ) ≤ ALow 8 := by
  norm_num [ALow, fLow, logLowRat]

private theorem ALow_sixteen_ge : (29813 / 100000 : ℝ) ≤ ALow 16 := by
  norm_num [ALow, fLow, logLowRat]

private theorem ALow_twentyfour_ge : (34322 / 100000 : ℝ) ≤ ALow 24 := by
  norm_num [ALow, fLow, logLowRat]

private theorem ALow_zero_le : ALow 0 ≤ Aprime (2 : ℝ) := by
  convert ALow_le_Aprime 0 (by norm_num) using 1
  norm_num

private theorem ALow_eight_le : ALow 8 ≤ Aprime (5 / 2 : ℝ) := by
  convert ALow_le_Aprime 8 (by norm_num) using 1
  norm_num

private theorem ALow_sixteen_le : ALow 16 ≤ Aprime (3 : ℝ) := by
  convert ALow_le_Aprime 16 (by norm_num) using 1
  norm_num

private theorem ALow_twentyfour_le : ALow 24 ≤ Aprime (7 / 2 : ℝ) := by
  convert ALow_le_Aprime 24 (by norm_num) using 1
  norm_num

private lemma cell_all (k : ℕ) (h30 : 30 ≤ k) (h69 : k ≤ 69) :
    ∃ E : ℝ, envNum (3/2 + ((k : ℕ) : ℝ)/20) ≤ E ∧ 0 ≤ E ∧
      1 + E / (3/2 + ((k : ℕ) : ℝ)/20) + 1/1000
        ≤ ((Submission.ChenPlan.utabList.getD k 0 : ℚ) : ℝ) := by
  interval_cases k
  · -- k = 30
    refine ⟨(1423/2500 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (0 : ℝ) ≤ Aprime (2 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (2 : ℝ)) (Am := ALow 0) (x := (2 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_zero_le)
      have h1 : (0 : ℝ) ≤ ALow 0 := ALow_zero_ge
      have h2 : ((0 : ℝ) - (0 : ℝ)) ≤ ((2 : ℝ) - (2 : ℝ)) * fLow (((2 : ℝ) + (2 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((2 : ℝ)/2) ≤ (0 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (2 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((30 : ℕ) : ℝ)/20) - 1 = (2 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (2 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 31
    refine ⟨(52139727/100000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (26514293/1000000000 : ℝ) ≤ Aprime (41/20 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (2 : ℝ)) (Am := ALow 0) (x := (41/20 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_zero_le)
      have h1 : (0 : ℝ) ≤ ALow 0 := ALow_zero_ge
      have h2 : ((26514293/1000000000 : ℝ) - (0 : ℝ)) ≤ ((41/20 : ℝ) - (2 : ℝ)) * fLow (((2 : ℝ) + (41/20 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((41/20 : ℝ)/2) ≤ (24692613/1000000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (41/20 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((31 : ℕ) : ℝ)/20) - 1 = (41/20 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (41/20 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 32
    refine ⟨(11944041/25000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (51207273/1000000000 : ℝ) ≤ Aprime (21/10 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (2 : ℝ)) (Am := ALow 0) (x := (21/10 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_zero_le)
      have h1 : (0 : ℝ) ≤ ALow 0 := ALow_zero_ge
      have h2 : ((51207273/1000000000 : ℝ) - (0 : ℝ)) ≤ ((21/10 : ℝ) - (2 : ℝ)) * fLow (((2 : ℝ) + (21/10 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((21/10 : ℝ)/2) ≤ (9758033/200000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (21/10 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((32 : ℕ) : ℝ)/20) - 1 = (21/10 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (21/10 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 33
    refine ⟨(21901127/50000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (14837103/200000000 : ℝ) ≤ Aprime (43/20 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (2 : ℝ)) (Am := ALow 0) (x := (43/20 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_zero_le)
      have h1 : (0 : ℝ) ≤ ALow 0 := ALow_zero_ge
      have h2 : ((14837103/200000000 : ℝ) - (0 : ℝ)) ≤ ((43/20 : ℝ) - (2 : ℝ)) * fLow (((2 : ℝ) + (43/20 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((43/20 : ℝ)/2) ≤ (36160331/500000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (43/20 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((33 : ℕ) : ℝ)/20) - 1 = (43/20 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (43/20 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 34
    refine ⟨(40192861/100000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (95548097/1000000000 : ℝ) ≤ Aprime (11/5 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (2 : ℝ)) (Am := ALow 0) (x := (11/5 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_zero_le)
      have h1 : (0 : ℝ) ≤ ALow 0 := ALow_zero_ge
      have h2 : ((95548097/1000000000 : ℝ) - (0 : ℝ)) ≤ ((11/5 : ℝ) - (2 : ℝ)) * fLow (((2 : ℝ) + (11/5 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((11/5 : ℝ)/2) ≤ (4765509/50000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (11/5 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((34 : ℕ) : ℝ)/20) - 1 = (11/5 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (11/5 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 35
    refine ⟨(18462303/50000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (23077447/200000000 : ℝ) ≤ Aprime (9/4 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (2 : ℝ)) (Am := ALow 0) (x := (9/4 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_zero_le)
      have h1 : (0 : ℝ) ≤ ALow 0 := ALow_zero_ge
      have h2 : ((23077447/200000000 : ℝ) - (0 : ℝ)) ≤ ((9/4 : ℝ) - (2 : ℝ)) * fLow (((2 : ℝ) + (9/4 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((9/4 : ℝ)/2) ≤ (29445759/250000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (9/4 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((35 : ℕ) : ℝ)/20) - 1 = (9/4 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (9/4 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 36
    refine ⟨(33975729/100000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (66894427/500000000 : ℝ) ≤ Aprime (23/10 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (2 : ℝ)) (Am := ALow 0) (x := (23/10 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_zero_le)
      have h1 : (0 : ℝ) ≤ ALow 0 := ALow_zero_ge
      have h2 : ((66894427/500000000 : ℝ) - (0 : ℝ)) ≤ ((23/10 : ℝ) - (2 : ℝ)) * fLow (((2 : ℝ) + (23/10 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((23/10 : ℝ)/2) ≤ (139761943/1000000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (23/10 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((36 : ℕ) : ℝ)/20) - 1 = (23/10 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (23/10 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 37
    refine ⟨(6265191/20000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (75416549/500000000 : ℝ) ≤ Aprime (47/20 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (2 : ℝ)) (Am := ALow 0) (x := (47/20 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_zero_le)
      have h1 : (0 : ℝ) ≤ ALow 0 := ALow_zero_ge
      have h2 : ((75416549/500000000 : ℝ) - (0 : ℝ)) ≤ ((47/20 : ℝ) - (2 : ℝ)) * fLow (((2 : ℝ) + (47/20 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((47/20 : ℝ)/2) ≤ (40317037/250000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (47/20 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((37 : ℕ) : ℝ)/20) - 1 = (47/20 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (47/20 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 38
    refine ⟨(28956381/100000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (33318961/200000000 : ℝ) ≤ Aprime (12/5 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (2 : ℝ)) (Am := ALow 0) (x := (12/5 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_zero_le)
      have h1 : (0 : ℝ) ≤ ALow 0 := ALow_zero_ge
      have h2 : ((33318961/200000000 : ℝ) - (0 : ℝ)) ≤ ((12/5 : ℝ) - (2 : ℝ)) * fLow (((2 : ℝ) + (12/5 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((12/5 : ℝ)/2) ≤ (182321557/1000000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (12/5 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((38 : ℕ) : ℝ)/20) - 1 = (12/5 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (12/5 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 39
    refine ⟨(5369873/20000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (2264299/12500000 : ℝ) ≤ Aprime (49/20 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (2 : ℝ)) (Am := ALow 0) (x := (49/20 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_zero_le)
      have h1 : (0 : ℝ) ≤ ALow 0 := ALow_zero_ge
      have h2 : ((2264299/12500000 : ℝ) - (0 : ℝ)) ≤ ((49/20 : ℝ) - (2 : ℝ)) * fLow (((2 : ℝ) + (49/20 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((49/20 : ℝ)/2) ≤ (40588169/200000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (49/20 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((39 : ℕ) : ℝ)/20) - 1 = (49/20 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (49/20 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 40
    refine ⟨(23591401/100000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (9923/50000 : ℝ) ≤ Aprime (5/2 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (5/2 : ℝ)) (Am := ALow 8) (x := (5/2 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_eight_le)
      have h1 : (19846/100000 : ℝ) ≤ ALow 8 := ALow_eight_ge
      have h2 : ((9923/50000 : ℝ) - (19846/100000 : ℝ)) ≤ ((5/2 : ℝ) - (5/2 : ℝ)) * fLow (((5/2 : ℝ) + (5/2 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((5/2 : ℝ)/2) ≤ (1743309/7812500 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (5/2 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((40 : ℕ) : ℝ)/20) - 1 = (5/2 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (5/2 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 41
    refine ⟨(1078743/5000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (52964589/250000000 : ℝ) ≤ Aprime (51/20 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (5/2 : ℝ)) (Am := ALow 8) (x := (51/20 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_eight_le)
      have h1 : (19846/100000 : ℝ) ≤ ALow 8 := ALow_eight_ge
      have h2 : ((52964589/250000000 : ℝ) - (19846/100000 : ℝ)) ≤ ((51/20 : ℝ) - (5/2 : ℝ)) * fLow (((5/2 : ℝ) + (51/20 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((51/20 : ℝ)/2) ≤ (242946179/1000000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (51/20 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((41 : ℕ) : ℝ)/20) - 1 = (51/20 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (51/20 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 42
    refine ⟨(9864441/50000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (11217817/50000000 : ℝ) ≤ Aprime (13/5 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (5/2 : ℝ)) (Am := ALow 8) (x := (13/5 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_eight_le)
      have h1 : (19846/100000 : ℝ) ≤ ALow 8 := ALow_eight_ge
      have h2 : ((11217817/50000000 : ℝ) - (19846/100000 : ℝ)) ≤ ((13/5 : ℝ) - (5/2 : ℝ)) * fLow (((5/2 : ℝ) + (13/5 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((13/5 : ℝ)/2) ≤ (52472853/200000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (13/5 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((42 : ℕ) : ℝ)/20) - 1 = (13/5 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (13/5 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 43
    refine ⟨(4511111/25000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (235995329/1000000000 : ℝ) ≤ Aprime (53/20 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (5/2 : ℝ)) (Am := ALow 8) (x := (53/20 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_eight_le)
      have h1 : (19846/100000 : ℝ) ≤ ALow 8 := ALow_eight_ge
      have h2 : ((235995329/1000000000 : ℝ) - (19846/100000 : ℝ)) ≤ ((53/20 : ℝ) - (5/2 : ℝ)) * fLow (((5/2 : ℝ) + (53/20 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((53/20 : ℝ)/2) ≤ (281412461/1000000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (53/20 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((43 : ℕ) : ℝ)/20) - 1 = (53/20 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (53/20 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 44
    refine ⟨(16512993/100000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (3085181/12500000 : ℝ) ≤ Aprime (27/10 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (5/2 : ℝ)) (Am := ALow 8) (x := (27/10 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_eight_le)
      have h1 : (19846/100000 : ℝ) ≤ ALow 8 := ALow_eight_ge
      have h2 : ((3085181/12500000 : ℝ) - (19846/100000 : ℝ)) ≤ ((27/10 : ℝ) - (5/2 : ℝ)) * fLow (((5/2 : ℝ) + (27/10 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((27/10 : ℝ)/2) ≤ (150052297/500000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (27/10 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((44 : ℕ) : ℝ)/20) - 1 = (27/10 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (27/10 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 45
    refine ⟨(15126419/100000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (32106359/125000000 : ℝ) ≤ Aprime (11/4 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (5/2 : ℝ)) (Am := ALow 8) (x := (11/4 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_eight_le)
      have h1 : (19846/100000 : ℝ) ≤ ALow 8 := ALow_eight_ge
      have h2 : ((32106359/125000000 : ℝ) - (19846/100000 : ℝ)) ≤ ((11/4 : ℝ) - (5/2 : ℝ)) * fLow (((5/2 : ℝ) + (11/4 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((11/4 : ℝ)/2) ≤ (159226867/500000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (11/4 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((45 : ℕ) : ℝ)/20) - 1 = (11/4 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (11/4 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 46
    refine ⟨(1734629/12500000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (266139633/1000000000 : ℝ) ≤ Aprime (14/5 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (5/2 : ℝ)) (Am := ALow 8) (x := (14/5 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_eight_le)
      have h1 : (19846/100000 : ℝ) ≤ ALow 8 := ALow_eight_ge
      have h2 : ((266139633/1000000000 : ℝ) - (19846/100000 : ℝ)) ≤ ((14/5 : ℝ) - (5/2 : ℝ)) * fLow (((5/2 : ℝ) + (14/5 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((14/5 : ℝ)/2) ≤ (168236121/500000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (14/5 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((46 : ℕ) : ℝ)/20) - 1 = (14/5 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (14/5 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 47
    refine ⟨(398673/3125000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (137357033/500000000 : ℝ) ≤ Aprime (57/20 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (5/2 : ℝ)) (Am := ALow 8) (x := (57/20 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_eight_le)
      have h1 : (19846/100000 : ℝ) ≤ ALow 8 := ALow_eight_ge
      have h2 : ((137357033/500000000 : ℝ) - (19846/100000 : ℝ)) ≤ ((57/20 : ℝ) - (5/2 : ℝ)) * fLow (((5/2 : ℝ) + (57/20 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((57/20 : ℝ)/2) ≤ (354171823/1000000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (57/20 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((47 : ℕ) : ℝ)/20) - 1 = (57/20 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (57/20 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 48
    refine ⟨(11761007/100000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (141302881/500000000 : ℝ) ≤ Aprime (29/10 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (5/2 : ℝ)) (Am := ALow 8) (x := (29/10 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_eight_le)
      have h1 : (19846/100000 : ℝ) ≤ ALow 8 := ALow_eight_ge
      have h2 : ((141302881/500000000 : ℝ) - (19846/100000 : ℝ)) ≤ ((29/10 : ℝ) - (5/2 : ℝ)) * fLow (((5/2 : ℝ) + (29/10 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((29/10 : ℝ)/2) ≤ (92890893/250000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (29/10 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((48 : ℕ) : ℝ)/20) - 1 = (29/10 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (29/10 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 49
    refine ⟨(10880871/100000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (2898447/10000000 : ℝ) ≤ Aprime (59/20 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (5/2 : ℝ)) (Am := ALow 8) (x := (59/20 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_eight_le)
      have h1 : (19846/100000 : ℝ) ≤ ALow 8 := ALow_eight_ge
      have h2 : ((2898447/10000000 : ℝ) - (19846/100000 : ℝ)) ≤ ((59/20 : ℝ) - (5/2 : ℝ)) * fLow (((5/2 : ℝ) + (59/20 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((59/20 : ℝ)/2) ≤ (77731603/200000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (59/20 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((49 : ℕ) : ℝ)/20) - 1 = (59/20 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (59/20 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 50
    refine ⟨(4757299/50000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (29813/100000 : ℝ) ≤ Aprime (3 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (3 : ℝ)) (Am := ALow 16) (x := (3 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_sixteen_le)
      have h1 : (29813/100000 : ℝ) ≤ ALow 16 := ALow_sixteen_ge
      have h2 : ((29813/100000 : ℝ) - (29813/100000 : ℝ)) ≤ ((3 : ℝ) - (3 : ℝ)) * fLow (((3 : ℝ) + (3 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((3 : ℝ)/2) ≤ (405465147/1000000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (3 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((50 : ℕ) : ℝ)/20) - 1 = (3 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (3 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 51
    refine ⟨(1084727/12500000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (304626571/1000000000 : ℝ) ≤ Aprime (61/20 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (3 : ℝ)) (Am := ALow 16) (x := (61/20 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_sixteen_le)
      have h1 : (29813/100000 : ℝ) ≤ ALow 16 := ALow_sixteen_ge
      have h2 : ((304626571/1000000000 : ℝ) - (29813/100000 : ℝ)) ≤ ((61/20 : ℝ) - (3 : ℝ)) * fLow (((3 : ℝ) + (61/20 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((61/20 : ℝ)/2) ≤ (42199447/100000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (61/20 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((51 : ℕ) : ℝ)/20) - 1 = (61/20 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (61/20 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 52
    refine ⟨(1583447/20000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (38826793/125000000 : ℝ) ≤ Aprime (31/10 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (3 : ℝ)) (Am := ALow 16) (x := (31/10 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_sixteen_le)
      have h1 : (29813/100000 : ℝ) ≤ ALow 16 := ALow_sixteen_ge
      have h2 : ((38826793/125000000 : ℝ) - (29813/100000 : ℝ)) ≤ ((31/10 : ℝ) - (3 : ℝ)) * fLow (((3 : ℝ) + (31/10 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((31/10 : ℝ)/2) ≤ (438255021/1000000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (31/10 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((52 : ℕ) : ℝ)/20) - 1 = (31/10 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (31/10 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 53
    refine ⟨(1807303/25000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (158056491/500000000 : ℝ) ≤ Aprime (63/20 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (3 : ℝ)) (Am := ALow 16) (x := (63/20 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_sixteen_le)
      have h1 : (29813/100000 : ℝ) ≤ ALow 16 := ALow_sixteen_ge
      have h2 : ((158056491/500000000 : ℝ) - (29813/100000 : ℝ)) ≤ ((63/20 : ℝ) - (3 : ℝ)) * fLow (((3 : ℝ) + (63/20 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((63/20 : ℝ)/2) ≤ (90851081/200000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (63/20 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((53 : ℕ) : ℝ)/20) - 1 = (63/20 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (63/20 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 54
    refine ⟨(6610251/100000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (160570643/500000000 : ℝ) ≤ Aprime (16/5 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (3 : ℝ)) (Am := ALow 16) (x := (16/5 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_sixteen_le)
      have h1 : (29813/100000 : ℝ) ≤ ALow 16 := ALow_sixteen_ge
      have h2 : ((160570643/500000000 : ℝ) - (29813/100000 : ℝ)) ≤ ((16/5 : ℝ) - (3 : ℝ)) * fLow (((3 : ℝ) + (16/5 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((16/5 : ℝ)/2) ≤ (23500191/50000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (16/5 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((54 : ℕ) : ℝ)/20) - 1 = (16/5 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (16/5 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 55
    refine ⟨(6056999/100000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (162858619/500000000 : ℝ) ≤ Aprime (13/4 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (3 : ℝ)) (Am := ALow 16) (x := (13/4 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_sixteen_le)
      have h1 : (29813/100000 : ℝ) ≤ ALow 16 := ALow_sixteen_ge
      have h2 : ((162858619/500000000 : ℝ) - (29813/100000 : ℝ)) ≤ ((13/4 : ℝ) - (3 : ℝ)) * fLow (((3 : ℝ) + (13/4 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((13/4 : ℝ)/2) ≤ (97101617/200000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (13/4 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((55 : ℕ) : ℝ)/20) - 1 = (13/4 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (13/4 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 56
    refine ⟨(1391561/25000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (164929021/500000000 : ℝ) ≤ Aprime (33/10 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (3 : ℝ)) (Am := ALow 16) (x := (33/10 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_sixteen_le)
      have h1 : (29813/100000 : ℝ) ≤ ALow 16 := ALow_sixteen_ge
      have h2 : ((164929021/500000000 : ℝ) - (29813/100000 : ℝ)) ≤ ((33/10 : ℝ) - (3 : ℝ)) * fLow (((3 : ℝ) + (33/10 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((33/10 : ℝ)/2) ≤ (500775663/1000000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (33/10 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((56 : ℕ) : ℝ)/20) - 1 = (33/10 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (33/10 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 57
    refine ⟨(5134903/100000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (333580163/1000000000 : ℝ) ≤ Aprime (67/20 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (3 : ℝ)) (Am := ALow 16) (x := (67/20 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_sixteen_le)
      have h1 : (29813/100000 : ℝ) ≤ ALow 16 := ALow_sixteen_ge
      have h2 : ((333580163/1000000000 : ℝ) - (29813/100000 : ℝ)) ≤ ((67/20 : ℝ) - (3 : ℝ)) * fLow (((3 : ℝ) + (67/20 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((67/20 : ℝ)/2) ≤ (515813679/1000000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (67/20 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((57 : ℕ) : ℝ)/20) - 1 = (67/20 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (67/20 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 58
    refine ⟨(238001/5000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (168449683/500000000 : ℝ) ≤ Aprime (17/5 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (3 : ℝ)) (Am := ALow 16) (x := (17/5 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_sixteen_le)
      have h1 : (29813/100000 : ℝ) ≤ ALow 16 := ALow_sixteen_ge
      have h2 : ((168449683/500000000 : ℝ) - (29813/100000 : ℝ)) ≤ ((17/5 : ℝ) - (3 : ℝ)) * fLow (((3 : ℝ) + (17/5 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((17/5 : ℝ)/2) ≤ (265314473/500000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (17/5 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((58 : ℕ) : ℝ)/20) - 1 = (17/5 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (17/5 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 59
    refine ⟨(4438761/100000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (339830749/1000000000 : ℝ) ≤ Aprime (69/20 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (3 : ℝ)) (Am := ALow 16) (x := (69/20 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_sixteen_le)
      have h1 : (29813/100000 : ℝ) ≤ ALow 16 := ALow_sixteen_ge
      have h2 : ((339830749/1000000000 : ℝ) - (29813/100000 : ℝ)) ≤ ((69/20 : ℝ) - (3 : ℝ)) * fLow (((3 : ℝ) + (69/20 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((69/20 : ℝ)/2) ≤ (545227977/1000000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (69/20 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((59 : ℕ) : ℝ)/20) - 1 = (69/20 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (69/20 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 60
    refine ⟨(3871729/100000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (17161/50000 : ℝ) ≤ Aprime (7/2 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (7/2 : ℝ)) (Am := ALow 24) (x := (7/2 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_twentyfour_le)
      have h1 : (34322/100000 : ℝ) ≤ ALow 24 := ALow_twentyfour_ge
      have h2 : ((17161/50000 : ℝ) - (34322/100000 : ℝ)) ≤ ((7/2 : ℝ) - (7/2 : ℝ)) * fLow (((7/2 : ℝ) + (7/2 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((7/2 : ℝ)/2) ≤ (55961701/100000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (7/2 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((60 : ℕ) : ℝ)/20) - 1 = (7/2 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (7/2 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 61
    refine ⟨(890429/25000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (345664981/1000000000 : ℝ) ≤ Aprime (71/20 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (7/2 : ℝ)) (Am := ALow 24) (x := (71/20 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_twentyfour_le)
      have h1 : (34322/100000 : ℝ) ≤ ALow 24 := ALow_twentyfour_ge
      have h2 : ((345664981/1000000000 : ℝ) - (34322/100000 : ℝ)) ≤ ((71/20 : ℝ) - (7/2 : ℝ)) * fLow (((7/2 : ℝ) + (71/20 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((71/20 : ℝ)/2) ≤ (114760403/200000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (71/20 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((61 : ℕ) : ℝ)/20) - 1 = (71/20 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (71/20 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 62
    refine ⟨(657057/20000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (173898999/500000000 : ℝ) ≤ Aprime (18/5 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (7/2 : ℝ)) (Am := ALow 24) (x := (18/5 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_twentyfour_le)
      have h1 : (34322/100000 : ℝ) ≤ ALow 24 := ALow_twentyfour_ge
      have h2 : ((173898999/500000000 : ℝ) - (34322/100000 : ℝ)) ≤ ((18/5 : ℝ) - (7/2 : ℝ)) * fLow (((7/2 : ℝ) + (18/5 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((18/5 : ℝ)/2) ≤ (587788719/1000000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (18/5 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((62 : ℕ) : ℝ)/20) - 1 = (18/5 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (18/5 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 63
    refine ⟨(608163/20000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (174814813/500000000 : ℝ) ≤ Aprime (73/20 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (7/2 : ℝ)) (Am := ALow 24) (x := (73/20 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_twentyfour_le)
      have h1 : (34322/100000 : ℝ) ≤ ALow 24 := ALow_twentyfour_ge
      have h2 : ((174814813/500000000 : ℝ) - (34322/100000 : ℝ)) ≤ ((73/20 : ℝ) - (7/2 : ℝ)) * fLow (((7/2 : ℝ) + (73/20 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((73/20 : ℝ)/2) ≤ (60158261/100000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (73/20 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((63 : ℕ) : ℝ)/20) - 1 = (73/20 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (73/20 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 64
    refine ⟨(1413369/50000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (175585023/500000000 : ℝ) ≤ Aprime (37/10 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (7/2 : ℝ)) (Am := ALow 24) (x := (37/10 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_twentyfour_le)
      have h1 : (34322/100000 : ℝ) ≤ ALow 24 := ALow_twentyfour_ge
      have h2 : ((175585023/500000000 : ℝ) - (34322/100000 : ℝ)) ≤ ((37/10 : ℝ) - (7/2 : ℝ)) * fLow (((7/2 : ℝ) + (37/10 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((37/10 : ℝ)/2) ≤ (615188959/1000000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (37/10 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((64 : ℕ) : ℝ)/20) - 1 = (37/10 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (37/10 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 65
    refine ⟨(2641539/100000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (352429061/1000000000 : ℝ) ≤ Aprime (15/4 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (7/2 : ℝ)) (Am := ALow 24) (x := (15/4 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_twentyfour_le)
      have h1 : (34322/100000 : ℝ) ≤ ALow 24 := ALow_twentyfour_ge
      have h2 : ((352429061/1000000000 : ℝ) - (34322/100000 : ℝ)) ≤ ((15/4 : ℝ) - (7/2 : ℝ)) * fLow (((7/2 : ℝ) + (15/4 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((15/4 : ℝ)/2) ≤ (25144513/40000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (15/4 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((65 : ℕ) : ℝ)/20) - 1 = (15/4 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (15/4 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 66
    refine ⟨(1241879/50000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (88354027/250000000 : ℝ) ≤ Aprime (19/5 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (7/2 : ℝ)) (Am := ALow 24) (x := (19/5 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_twentyfour_le)
      have h1 : (34322/100000 : ℝ) ≤ ALow 24 := ALow_twentyfour_ge
      have h2 : ((88354027/250000000 : ℝ) - (34322/100000 : ℝ)) ≤ ((19/5 : ℝ) - (7/2 : ℝ)) * fLow (((7/2 : ℝ) + (19/5 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((19/5 : ℝ)/2) ≤ (64185907/100000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (19/5 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((66 : ℕ) : ℝ)/20) - 1 = (19/5 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (19/5 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 67
    refine ⟨(1175991/50000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (88535069/250000000 : ℝ) ≤ Aprime (77/20 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (7/2 : ℝ)) (Am := ALow 24) (x := (77/20 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_twentyfour_le)
      have h1 : (34322/100000 : ℝ) ≤ ALow 24 := ALow_twentyfour_ge
      have h2 : ((88535069/250000000 : ℝ) - (34322/100000 : ℝ)) ≤ ((77/20 : ℝ) - (7/2 : ℝ)) * fLow (((7/2 : ℝ) + (77/20 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((77/20 : ℝ)/2) ≤ (65493237/100000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (77/20 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((67 : ℕ) : ℝ)/20) - 1 = (77/20 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (77/20 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 68
    refine ⟨(44897/2000000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (177305163/500000000 : ℝ) ≤ Aprime (39/10 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (7/2 : ℝ)) (Am := ALow 24) (x := (39/10 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_twentyfour_le)
      have h1 : (34322/100000 : ℝ) ≤ ALow 24 := ALow_twentyfour_ge
      have h2 : ((177305163/500000000 : ℝ) - (34322/100000 : ℝ)) ≤ ((39/10 : ℝ) - (7/2 : ℝ)) * fLow (((7/2 : ℝ) + (39/10 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((39/10 : ℝ)/2) ≤ (667837223/1000000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (39/10 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((68 : ℕ) : ℝ)/20) - 1 = (39/10 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (39/10 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]
  · -- k = 69
    refine ⟨(270131/12500000 : ℝ), ?_, by norm_num, by norm_num [Submission.ChenPlan.utabList]⟩
    have hA : (177417347/500000000 : ℝ) ≤ Aprime (79/20 : ℝ) := by
      refine le_trans ?_ (Abnd_le_Aprime (a := (7/2 : ℝ)) (Am := ALow 24) (x := (79/20 : ℝ))
        (by norm_num) (by norm_num) (by norm_num) ALow_twentyfour_le)
      have h1 : (34322/100000 : ℝ) ≤ ALow 24 := ALow_twentyfour_ge
      have h2 : ((177417347/500000000 : ℝ) - (34322/100000 : ℝ)) ≤ ((79/20 : ℝ) - (7/2 : ℝ)) * fLow (((7/2 : ℝ) + (79/20 : ℝ))/2) := by
        norm_num [fLow, logLowRat]
      linarith
    have hL : Real.log ((79/20 : ℝ)/2) ≤ (680577959/1000000000 : ℝ) := by
      refine le_trans (le_logUpRat (by norm_num : (1:ℝ) ≤ (79/20 : ℝ)/2)) ?_
      norm_num [logUpRat]
    have hs : (3/2 + ((69 : ℕ) : ℝ)/20) - 1 = (79/20 : ℝ) := by norm_num
    rw [envNum, hs, min_eq_left (by norm_num : (79/20 : ℝ) ≤ 4), envC, envT]
    linarith [hA, hL]

private lemma tab_small (k : ℕ) (hk : k ≤ 30) :
    (3578 : ℝ)/1000 ≤ (3/2 + ((k : ℕ) : ℝ)/20)
        * (((Submission.ChenPlan.utabList.getD k 0 : ℚ) : ℝ) - 1/1000)
      ∧ (1 : ℝ) ≤ ((Submission.ChenPlan.utabList.getD k 0 : ℚ) : ℝ) := by
  interval_cases k <;> norm_num [Submission.ChenPlan.utabList]

/-! ## §5  The main theorem -/

theorem riUp_le_Utab (s : ℝ) (hs : 1 ≤ s) :
    1 + Work.NumberTheory.Chen.APSwitchUpper.riPhi s + 1/1000 ≤ Submission.ChenPlan.Utab s := by
  have hs0 : (0 : ℝ) < s := by linarith
  have hexp : (7 : ℝ) / 4 ≤ Real.exp Real.eulerMascheroniConstant := by
    have h := Work.NumberTheory.Chen.ApSumTenth.twoExpGamma_ge_seven_halves
    unfold Work.NumberTheory.Chen.ApSumTenth.twoExpGamma at h
    linarith
  rcases lt_or_ge s (3 / 2) with h32 | h32
  · -- `s < 3/2`: both sides are the Selberg shape
    have hri : (1 : ℝ) + riPhi s = 2 * Real.exp Real.eulerMascheroniConstant / s :=
      Work.NumberTheory.Chen.BTermCount.riUp_eq_twoExpGamma_div s hs (by linarith)
    rw [Submission.ChenPlan.Utab, if_pos h32, hri]
    have h1 : 2 * Real.exp Real.eulerMascheroniConstant / s + 1 / 1000
        = (2 * Real.exp Real.eulerMascheroniConstant + s * (1 / 1000)) / s := by
      field_simp
    rw [h1, show (1005 : ℝ) / 1000 * (2 * Real.exp Real.eulerMascheroniConstant) / s
        = (1005 / 1000 * (2 * Real.exp Real.eulerMascheroniConstant)) / s by ring,
      div_le_div_iff_of_pos_right hs0]
    nlinarith [hexp, h32]
  rcases lt_or_ge s 3 with h3 | h3
  · -- `3/2 ≤ s < 3`: the closed form `riUp s = 2e^γ/s` and the first 31 table entries
    have hri : (1 : ℝ) + riPhi s = 2 * Real.exp Real.eulerMascheroniConstant / s :=
      Work.NumberTheory.Chen.BTermCount.riUp_eq_twoExpGamma_div s hs (le_of_lt h3)
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k = min (⌊(s - 3 / 2) * 20⌋₊) 70 := ⟨_, rfl⟩
    have hfloor : ((⌊(s - 3 / 2) * 20⌋₊ : ℕ) : ℝ) ≤ (s - 3 / 2) * 20 :=
      Nat.floor_le (by linarith)
    have hk30 : k ≤ 30 := by
      rw [hk]
      refine le_trans (min_le_left _ _) ?_
      by_contra hcon
      push_neg at hcon
      have h31 : (31 : ℝ) ≤ ((⌊(s - 3 / 2) * 20⌋₊ : ℕ) : ℝ) := by exact_mod_cast hcon
      linarith
    have hsge : 3 / 2 + ((k : ℕ) : ℝ) / 20 ≤ s := by
      rw [hk]
      have h1 : ((min (⌊(s - 3 / 2) * 20⌋₊) 70 : ℕ) : ℝ)
          ≤ ((⌊(s - 3 / 2) * 20⌋₊ : ℕ) : ℝ) := by exact_mod_cast min_le_left _ _
      linarith
    have hUtab : Submission.ChenPlan.Utab s
        = ((Submission.ChenPlan.utabList.getD k 0 : ℚ) : ℝ) := by
      rw [Submission.ChenPlan.Utab, if_neg (not_lt.mpr h32), ← hk]
    rw [hUtab, hri]
    obtain ⟨ht, ht1⟩ := tab_small k hk30
    have hγ := twoExpGamma_le_3578
    have ht0 : (0 : ℝ) ≤ ((Submission.ChenPlan.utabList.getD k 0 : ℚ) : ℝ) - 1 / 1000 := by
      linarith
    have hkey : 2 * Real.exp Real.eulerMascheroniConstant
        ≤ s * (((Submission.ChenPlan.utabList.getD k 0 : ℚ) : ℝ) - 1 / 1000) :=
      le_trans hγ (le_trans ht (mul_le_mul_of_nonneg_right hsge ht0))
    have hfin : 2 * Real.exp Real.eulerMascheroniConstant / s + 1 / 1000
        ≤ ((Submission.ChenPlan.utabList.getD k 0 : ℚ) : ℝ) := by
      have h1 : 2 * Real.exp Real.eulerMascheroniConstant / s + 1 / 1000
          = (2 * Real.exp Real.eulerMascheroniConstant + s * (1 / 1000)) / s := by
        field_simp
      rw [h1, div_le_iff₀ hs0]
      linarith
    exact hfin
  · -- `3 ≤ s`
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k = min (⌊(s - 3 / 2) * 20⌋₊) 70 := ⟨_, rfl⟩
    have hfloor : ((⌊(s - 3 / 2) * 20⌋₊ : ℕ) : ℝ) ≤ (s - 3 / 2) * 20 :=
      Nat.floor_le (by linarith)
    have hk30 : 30 ≤ k := by
      rw [hk]
      refine le_min ?_ (by norm_num)
      exact Nat.le_floor (by push_cast; linarith)
    have hsge : 3 / 2 + ((k : ℕ) : ℝ) / 20 ≤ s := by
      rw [hk]
      have h1 : ((min (⌊(s - 3 / 2) * 20⌋₊) 70 : ℕ) : ℝ)
          ≤ ((⌊(s - 3 / 2) * 20⌋₊ : ℕ) : ℝ) := by exact_mod_cast min_le_left _ _
      linarith
    have hUtab : Submission.ChenPlan.Utab s
        = ((Submission.ChenPlan.utabList.getD k 0 : ℚ) : ℝ) := by
      rw [Submission.ChenPlan.Utab, if_neg (not_lt.mpr h32), ← hk]
    have hphi : riPhi s ≤ riPhiEnv s := riPhi_le_env s (by linarith)
    rcases lt_or_ge s 5 with h5 | h5
    · -- `3 < s < 5`
      have hk69 : k ≤ 69 := by
        rw [hk]
        have hlt : ⌊(s - 3 / 2) * 20⌋₊ < 70 := by
          have := hfloor
          have h70 : ((⌊(s - 3 / 2) * 20⌋₊ : ℕ) : ℝ) < 70 := by linarith
          exact_mod_cast h70
        exact le_trans (min_le_left _ _) (by omega)
      obtain ⟨E, hE1, hE0, hE2⟩ := cell_all k hk30 hk69
      have hsk3 : (3 : ℝ) ≤ 3 / 2 + ((k : ℕ) : ℝ) / 20 := by
        have hk30' : (30 : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hk30
        linarith
      have hnum : envNum s ≤ E :=
        le_trans (envNum_antiOn hsk3 (show (3 : ℝ) ≤ s from h3) hsge) hE1
      have hsk : (0 : ℝ) < 3 / 2 + ((k : ℕ) : ℝ) / 20 := by positivity
      have hdiv1 : envNum s / s ≤ E / s := div_le_div_of_nonneg_right hnum hs0.le
      have hdiv2 : E / s ≤ E / (3 / 2 + ((k : ℕ) : ℝ) / 20) := by
        refine div_le_div_of_nonneg_left hE0 hsk ?_
        exact hsge
      have hmain : 1 + envNum s / s + 1 / 1000
          ≤ ((Submission.ChenPlan.utabList.getD k 0 : ℚ) : ℝ) := by
        linarith [hdiv1, hdiv2, hE2]
      rw [hUtab]
      calc 1 + riPhi s + 1 / 1000 ≤ 1 + riPhiEnv s + 1 / 1000 := by linarith
        _ = 1 + envNum s / s + 1 / 1000 := by rw [riPhiEnv_of_three_le (by linarith)]
        _ ≤ ((Submission.ChenPlan.utabList.getD k 0 : ℚ) : ℝ) := hmain
    · -- `5 ≤ s`
      have hmin70 : min (⌊(s - 3 / 2) * 20⌋₊) 70 = 70 := by
        refine min_eq_right ?_
        exact Nat.le_floor (by push_cast; linarith)
      have hU70 : Submission.ChenPlan.Utab s = (1008 / 1000 : ℝ) := by
        rw [Submission.ChenPlan.Utab, if_neg (not_lt.mpr h32), hmin70]
        norm_num [Submission.ChenPlan.utabList]
      have hnum5 : envNum 5 ≤ (98211/5000000 : ℝ) := by
        rw [envNum_of_five_le le_rfl, envC, envT]
        have hA4 := Aprime_four_ge_sharp
        have hL : Real.log 2 ≤ (693158749/1000000000 : ℝ) := by
          refine le_trans (le_logUpRat (by norm_num)) ?_
          norm_num [logUpRat]
        linarith
      have hdiv1 : envNum 5 / s ≤ (98211/5000000 : ℝ) / s := div_le_div_of_nonneg_right hnum5 hs0.le
      have hdiv2 : (98211/5000000 : ℝ) / s ≤ (98211/5000000 : ℝ) / 5 := by
        refine div_le_div_of_nonneg_left (by norm_num) (by norm_num) h5
      have hfin : 1 + (98211/5000000 : ℝ) / 5 + 1 / 1000 ≤ (1008 / 1000 : ℝ) := by
        norm_num
      rw [hU70]
      calc 1 + riPhi s + 1 / 1000 ≤ 1 + riPhiEnv s + 1 / 1000 := by linarith
        _ = 1 + envNum 5 / s + 1 / 1000 := by rw [riPhiEnv_of_five_le h5]
        _ ≤ 1 + (98211/5000000 : ℝ) / 5 + 1 / 1000 := by linarith [hdiv1, hdiv2]
        _ ≤ (1008 / 1000 : ℝ) := hfin

end

end Work.ChenPlan.LinearSieve.Numerics
