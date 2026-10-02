import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.OffAxis.RectC.Tiny
import Submission.Work.ZeroFreeTables.OffAxis.RectC.Facts
import Submission.Work.ZeroFreeTables.OffAxis.RectC.PrincipalHeight
import Submission.Work.ZeroFreeTables.OffAxis.RectC.Numeric95
import Submission.Work.ZeroFreeTables.OffAxis.RectC.Numeric95b
import Submission.Work.ZeroFreeTables.OffAxis.RectC.SecondMin
import Submission.Work.ZeroFreeTables.OffAxis.RectC.RectSelfMin
import Submission.Work.ZeroFreeTables.HB94.L52supply
import Submission.Work.ZeroFreeTables.HB94.L52supply18
import Submission.Work.ZeroFreeTables.HB94.L52supply_pow
import Submission.Work.ZeroFreeTables.HB94.Ksum_single_ne
import Submission.Work.ZeroFreeTables.HB94.HB94Aux
import Submission.Work.LinnikAreas.DhCapped.L52Hyp_mono
import Submission.Work.ZeroFreeTables.H4.Tf72FNegLamLe
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Commons.NumberTheory.Linnik.Ksum_principal_le
import Submission.Work.ZeroFreeTables.HB94.h5plus_cases

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

set_option maxHeartbeats 4000000

/-- Five `K`-sums bounded by `𝓛 · b_j` cannot satisfy the (9.15) combination when the rational
bracket `Σ c95_j b_j` is negative. -/
private theorem contrab5 {𝓛 B0 B1 B2 B3 B4 b0 b1 b2 b3 b4 : ℝ} (hL : 0 < 𝓛)
    (hcomb : 0 ≤ 14379 * B0 + 24480 * B1 + 14900 * B2 + 6000 * B3 + 1250 * B4)
    (h0 : B0 ≤ 𝓛 * b0) (h1 : B1 ≤ 𝓛 * b1) (h2 : B2 ≤ 𝓛 * b2) (h3 : B3 ≤ 𝓛 * b3)
    (h4 : B4 ≤ 𝓛 * b4)
    (hbr : (14379:ℝ) * b0 + 24480 * b1 + 14900 * b2 + 6000 * b3 + 1250 * b4 < 0) : False := by
  have e0 := mul_le_mul_of_nonneg_left h0 (by norm_num : (0:ℝ) ≤ 14379)
  have e1 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 24480)
  have e2 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 14900)
  have e3 := mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 6000)
  have e4 := mul_le_mul_of_nonneg_left h4 (by norm_num : (0:ℝ) ≤ 1250)
  have hsum : (14379:ℝ) * B0 + 24480 * B1 + 14900 * B2 + 6000 * B3 + 1250 * B4
      ≤ 14379 * (𝓛 * b0) + 24480 * (𝓛 * b1) + 14900 * (𝓛 * b2) + 6000 * (𝓛 * b3)
        + 1250 * (𝓛 * b4) := by linarith
  have hEq : (14379:ℝ) * (𝓛 * b0) + 24480 * (𝓛 * b1) + 14900 * (𝓛 * b2) + 6000 * (𝓛 * b3)
      + 1250 * (𝓛 * b4)
      = 𝓛 * (14379 * b0 + 24480 * b1 + 14900 * b2 + 6000 * b3 + 1250 * b4) := by ring
  have hneg : 𝓛 * ((14379:ℝ) * b0 + 24480 * b1 + 14900 * b2 + 6000 * b3 + 1250 * b4) < 0 :=
    mul_neg_of_pos_of_neg hL hbr
  linarith [hcomb, hsum, hEq, hneg]

-- HB Lemma 9.5 at rectangle height L (the `λ₁ ≥ 0.348` conjunct of `RectCertC`).
-- Recipe: transcribe `HBTheorem1_complex_h2` / `_h3` / `_h4` / `_h5plus`
-- (Submission/Work/ZeroFreeTables/HBTheorem1_complex_h{2,3,4,5plus}.lean) with the working
-- region `IsZ χ₁ ρ₁` (|Im ρ₁| ≤ 1, `IsMin1WideAt 10`) replaced by `IsRectMin L χ₁ ρ₁`
-- (|Im ρ₁| ≤ L, minimality over |Im| ≤ 10L), and with every height literal (3,4,10) scaled
-- by L.  q₀ is chosen so large that L ≤ log q, so the test points at heights ≤ 4L lie in the
-- range |t| ≤ 10 log q of the engine outputs (e.g. `k1_input` in HBLemma9_1_proof.lean takes
-- `|s.im| ≤ 10 * L` with L = log q).  The clean template for the transcription of the P₃ part
-- is `Submission/Work/ZeroFreeTables/HB94/Lam0GeEngine.lean` (`HBLemma9_1Wide_proof`, |t| ≤ 4,
-- |ρ₀| ≤ 2) obtained from HBLemma9_1_proof with |t| ≤ 3 → |t| ≤ 4.
theorem RectC_HB95 : ∀ L : ℝ, 1 ≤ L → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ),
    Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ → 1 < |ρ₁.im| →
      (348:ℝ)/1000 ≤ Work.LinnikContract.lamOf q ρ₁ := by
  intro L hL
  -- ## the `L52Hyp` supplies
  obtain ⟨δ16, hδ16pos, hδ16lt1, q16, h16raw⟩ := HB94.L52supply16
  obtain ⟨N18, δ18, hδ18pos, hδ18lt1, h18raw⟩ := HB94.L52supply18
  obtain ⟨δ60, hδ60pos, hδ60lt1, q60, h60raw⟩ := HB94.L52supply_pow
  set δ8 : ℝ := min δ18 δ60 with hδ8def
  have hδ8pos : 0 < δ8 := by rw [hδ8def]; exact lt_min hδ18pos hδ60pos
  have hδ8lt1 : δ8 < 1 := by rw [hδ8def]; exact lt_of_le_of_lt (min_le_left _ _) hδ18lt1
  have hδ8_18 : δ8 ≤ δ18 := by rw [hδ8def]; exact min_le_left _ _
  have hδ8_60 : δ8 ≤ δ60 := by rw [hδ8def]; exact min_le_right _ _
  have hL8 : ∀ q : ℕ, max N18 q60 ≤ q → ∀ [NeZero q] (χ : DirichletCharacter ℂ q)
      [NeZero χ.conductor], χ ≠ 1 →
      ((orderOf χ : ℝ) ≤ Real.log (((χ.conductor : ℕ) : ℝ)) ∨ χ ^ 60 = 1) →
      Commons.NumberTheory.Linnik.L52Hyp χ ((1:ℝ)/8) (1/1000000) δ8 := by
    intro q hq _inst χ _instc hχ hdisj
    rcases hdisj with hcond | hpow
    · exact Work.LinnikAreas.DhCapped.L52Hyp_mono χ hχ hδ8_18
        (h18raw q (le_trans (le_max_left _ _) hq) χ hχ hcond)
    · exact Work.LinnikAreas.DhCapped.L52Hyp_mono χ hχ hδ8_60
        (h60raw q (le_trans (le_max_right _ _) hq) χ hχ hpow)
  -- ## the test function `f = tf72f (3/4)`
  set f : ℝ → ℝ := tf72f ((3:ℝ)/4) with hfdef
  have h34 : (0:ℝ) < (3:ℝ)/4 := by norm_num
  have hfcont : ContinuousOn f (Set.Ici 0) := by rw [hfdef]; exact tf72f_cont _ h34
  have hfsupp : ∀ t : ℝ, (8:ℝ)/3 ≤ t → f t = 0 := by
    intro t ht
    have h2 : (2:ℝ) / ((3:ℝ)/4) = (8:ℝ)/3 := by norm_num
    rw [hfdef]; exact tf72f_supp _ h34 t (by rw [h2]; exact ht)
  have hfdiff : ContDiffOn ℝ 2 f (Set.Ioo 0 ((8:ℝ)/3)) := by
    have h2 : (2:ℝ) / ((3:ℝ)/4) = (8:ℝ)/3 := by norm_num
    rw [hfdef, ← h2]; exact tf72f_diff _ h34
  obtain ⟨B, hB0, hBnd⟩ := tf72f_bound ((3:ℝ)/4) h34
  have hfB : ∀ t ∈ Set.Ioo (0:ℝ) ((8:ℝ)/3), ‖iteratedDeriv 2 f t‖ ≤ B := by
    intro t ht
    have h2 : (2:ℝ) / ((3:ℝ)/4) = (8:ℝ)/3 := by norm_num
    rw [hfdef]; exact hBnd t (by rwa [← h2] at ht)
  have hfnn : ∀ t : ℝ, 0 ≤ f t := by rw [hfdef]; exact tf72f_nonneg _ h34
  have hf0pos : 0 < f 0 := by rw [hfdef, tf72f_at_zero _ h34]; norm_num
  have hf0val : f 0 = 4/5 := by rw [hfdef, tf72f_at_zero _ h34]; norm_num
  have hFc : ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..((8:ℝ)/3), Complex.exp (-(z * (t:ℂ))) * ((f t : ℝ):ℂ)).re := by
    intro z hz
    have h2 : (2:ℝ) / ((3:ℝ)/4) = (8:ℝ)/3 := by norm_num
    have h := tf72Fc_re_nonneg ((3:ℝ)/4) h34 z hz
    rw [hfdef, ← h2]; exact h
  have hF0 : (∫ t in (0:ℝ)..((8:ℝ)/3), f t) = 8/9 := by
    have h2 : (2:ℝ) / ((3:ℝ)/4) = (8:ℝ)/3 := by norm_num
    rw [hfdef, ← h2]; exact tf72f_intervalIntegral _ h34
  -- ## the five `K`-sum engines
  obtain ⟨qP, hKP⟩ := Commons.NumberTheory.Linnik.Ksum_principal_le ((8:ℝ)/3) B (by norm_num) hB0
    (f := f) hfcont hfsupp hfdiff hfB (ε := (1:ℝ)/1000000) (by norm_num) hf0pos
  obtain ⟨qS8, hKS8⟩ := Commons.NumberTheory.Linnik.Ksum_le_single_of_L52_phi ((8:ℝ)/3) B ((1:ℝ)/8)
    (by norm_num) hB0 (f := f) hfcont hfsupp hfdiff hfB hf0pos hFc
    (ε := (1:ℝ)/1000000) (by norm_num) hδ8pos hδ8lt1
  obtain ⟨qT8, hKT8⟩ := Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi ((8:ℝ)/3) B ((1:ℝ)/8)
    (by norm_num) hB0 (f := f) hfcont hfsupp hfdiff hfB hf0pos hFc
    (ε := (1:ℝ)/1000000) (by norm_num) hδ8pos hδ8lt1
  obtain ⟨qS16, hKS16⟩ := HB94.Ksum_le_single_of_L52_phi_ne ((8:ℝ)/3) B ((1:ℝ)/6)
    (by norm_num) hB0 (f := f) hfcont hfsupp hfdiff hfB hf0pos hFc
    (ε := (1:ℝ)/1000000) (by norm_num) hδ16pos hδ16lt1
  obtain ⟨qT16, hKT16⟩ := Commons.NumberTheory.Linnik.Ksum_le_self_of_L52_phi ((8:ℝ)/3) B ((1:ℝ)/6)
    (by norm_num) hB0 (f := f) hfcont hfsupp hfdiff hfB hf0pos hFc
    (ε := (1:ℝ)/1000000) (by norm_num) hδ16pos hδ16lt1
  obtain ⟨qPh, hKPh⟩ := RectC.PrincipalHeight ((8:ℝ)/3) B (by norm_num) hB0
    (f := f) hfcont hfsupp hfdiff hfB (ε := (1:ℝ)/1000000) (by norm_num) hf0pos
  obtain ⟨qSelf, hSelf⟩ := RectC.RectSelfMin L hL
  obtain ⟨qsec, hsecond⟩ := RectC.SecondMin L hL
  -- ## the threshold
  refine ⟨qP + qS8 + qT8 + qS16 + qT16 + qPh + qSelf + qsec + q16 + N18 + q60 + 1000000
    + (Nat.ceil (Real.exp L) + 1) + (Nat.ceil (Real.exp (348 / (1000 * δ8))) + 1)
    + (Nat.ceil (Real.exp (348 / (1000 * δ16))) + 1), ?_⟩
  intro q hq hqne χ₁ ρ₁ hR him1
  haveI : NeZero q := hqne
  have hqP : qP ≤ q := by omega
  have hqS8 : qS8 ≤ q := by omega
  have hqT8 : qT8 ≤ q := by omega
  have hqS16 : qS16 ≤ q := by omega
  have hqT16 : qT16 ≤ q := by omega
  have hqPh : qPh ≤ q := by omega
  have hqSelf : qSelf ≤ q := by omega
  have hqsec : qsec ≤ q := by omega
  have hq16 : q16 ≤ q := by omega
  have hqN18 : N18 ≤ q := by omega
  have hq60 : q60 ≤ q := by omega
  have hq8 : max N18 q60 ≤ q := max_le hqN18 hq60
  have hq1e6 : 1000000 ≤ q := by omega
  have hqL : Nat.ceil (Real.exp L) + 1 ≤ q := by omega
  have hqδ8 : Nat.ceil (Real.exp (348 / (1000 * δ8))) + 1 ≤ q := by omega
  have hqδ16 : Nat.ceil (Real.exp (348 / (1000 * δ16))) + 1 ≤ q := by omega
  by_contra hcon
  push Not at hcon
  have hsmall : Work.LinnikContract.lamOf q ρ₁ ≤ (348:ℝ)/1000 := le_of_lt hcon
  have hχ1 : χ₁ ≠ 1 := hR.1.1
  have hzm1 : Work.LinnikContract.zeroMult χ₁ ρ₁ ≠ 0 := hR.1.2.1
  have hγL : |ρ₁.im| ≤ L := hR.1.2.2
  have hq2 : 2 ≤ q := by omega
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hlogq : 0 < Real.log (q:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hlog6 : (6:ℝ) ≤ Real.log (q:ℝ) := by
    have h6 : (1000000:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1e6
    have h7 := Real.log_le_log (by norm_num : (0:ℝ) < 1000000) h6
    have h8 : Real.log (1000000:ℝ) = 6 * Real.log 10 := by
      rw [show (1000000:ℝ) = 10^6 by norm_num, Real.log_pow]; norm_num
    have h9 : (2:ℝ) ≤ Real.log 10 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 10)]
      have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith only [Real.exp_one_lt_three, Real.exp_pos 1, he]
    rw [h8] at h7; linarith
  have hLlog : L ≤ Real.log (q:ℝ) := by
    have h1 : Real.exp L ≤ (q:ℝ) := by
      have h2 : Real.exp L ≤ (Nat.ceil (Real.exp L) : ℝ) := Nat.le_ceil _
      have h3 : ((Nat.ceil (Real.exp L) : ℕ) : ℝ) + 1 ≤ (q:ℝ) := by exact_mod_cast hqL
      linarith
    calc L = Real.log (Real.exp L) := (Real.log_exp L).symm
      _ ≤ Real.log (q:ℝ) := Real.log_le_log (Real.exp_pos L) h1
  have hlamnn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    HB94.Lam0GeEngine.lamOf_nonneg_of_zeroMult hzm1
  haveI hc1 : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  -- the zero-free strip and the position of `ρ₁`
  have hstrip1 : 0 < ρ₁.re ∧ ρ₁.re < 1 :=
    Commons.NumberTheory.Linnik.completedL_zero_strip χ₁.primitiveCharacter
      (HB94.primitive_ne_one_aux χ₁ hχ1) (DirichletCharacter.primitiveCharacter_isPrimitive χ₁)
      (apply_eq_zero_of_analyticOrderNatAt_ne_zero
        (by simpa only [Work.LinnikContract.zeroMult] using hzm1))
  have hβlam : 1 - ρ₁.re = Work.LinnikContract.lamOf q ρ₁ / Real.log (q:ℝ) := by
    rw [Work.LinnikContract.lamOf]; field_simp
  have hnn1 : 0 ≤ 1 - ρ₁.re := by rw [hβlam]; exact div_nonneg hlamnn hlogq.le
  have hloglogge82 : (82:ℝ)/100 ≤ Real.log (Real.log (q:ℝ)) := by
    have h5 : Real.log 6 ≤ Real.log (Real.log (q:ℝ)) := Real.log_le_log (by norm_num) hlog6
    have h6 : (82:ℝ)/100 ≤ Real.log 6 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have h7 : Real.exp (82/100) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      linarith [Real.exp_one_lt_three, h7]
    linarith
  have hloglogge : (348:ℝ)/1000 ≤ Real.log (Real.log (q:ℝ)) := by linarith
  have hsqrtge348 : (348:ℝ)/1000 ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := by
    calc (348:ℝ)/1000 ≤ Real.sqrt ((348:ℝ)/1000) := by
          rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      _ ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := Real.sqrt_le_sqrt hloglogge
  have hsqrtge82 : (82:ℝ)/100 ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := by
    calc (82:ℝ)/100 ≤ Real.sqrt ((82:ℝ)/100) := by
          rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
      _ ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) := Real.sqrt_le_sqrt hloglogge82
  have hβre : |ρ₁.re - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
    have h2 : |ρ₁.re - 1| = 1 - ρ₁.re := by
      rw [abs_of_nonpos (by linarith [hstrip1.2])]; ring
    rw [h2, hβlam]
    exact div_le_div_of_nonneg_right (le_trans hsmall hsqrtge348) hlogq.le
  have hslo : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤ ρ₁.re := by
    have h1 : -|ρ₁.re - 1| ≤ ρ₁.re - 1 := neg_abs_le _
    linarith [hβre, h1]
  have hmem1 : ρ₁ ∈ Metric.closedBall (0:ℂ) (|ρ₁.im| + 2) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have hre : |ρ₁.re| ≤ 1 := by rw [abs_of_pos hstrip1.1]; exact hstrip1.2.le
    calc ‖ρ₁‖ ≤ |ρ₁.re| + |ρ₁.im| := Complex.norm_le_abs_re_add_abs_im ρ₁
      _ ≤ |ρ₁.im| + 1 := by linarith
      _ ≤ |ρ₁.im| + 2 := by linarith
  have hdiv1 : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
      (Metric.closedBall 0 (|ρ₁.im| + 2))) ρ₁ ≠ 0 :=
    divisor_ne_zero_of_zeroMult χ₁ hχ1 hmem1 hzm1
  have hδlog8 : (348:ℝ)/1000 ≤ δ8 * Real.log (q:ℝ) := by
    have h3 : Real.exp (348 / (1000 * δ8)) ≤ (q:ℝ) := by
      have h1 : Real.exp (348 / (1000 * δ8)) ≤ (Nat.ceil (Real.exp (348 / (1000 * δ8))) : ℝ) :=
        Nat.le_ceil _
      have h2 : ((Nat.ceil (Real.exp (348 / (1000 * δ8))) : ℕ) : ℝ) ≤ (q:ℝ) := by
        exact_mod_cast (by omega : Nat.ceil (Real.exp (348 / (1000 * δ8))) ≤ q)
      linarith
    have h4 : 348 / (1000 * δ8) ≤ Real.log (q:ℝ) := by
      rw [Real.le_log_iff_exp_le hqpos]; exact h3
    calc (348:ℝ)/1000 = δ8 * (348 / (1000 * δ8)) := by field_simp
      _ ≤ δ8 * Real.log (q:ℝ) := mul_le_mul_of_nonneg_left h4 hδ8pos.le
  have hδlog16 : (348:ℝ)/1000 ≤ δ16 * Real.log (q:ℝ) := by
    have h3 : Real.exp (348 / (1000 * δ16)) ≤ (q:ℝ) := by
      have h1 : Real.exp (348 / (1000 * δ16)) ≤ (Nat.ceil (Real.exp (348 / (1000 * δ16))) : ℝ) :=
        Nat.le_ceil _
      have h2 : ((Nat.ceil (Real.exp (348 / (1000 * δ16))) : ℕ) : ℝ) ≤ (q:ℝ) := by
        exact_mod_cast (by omega : Nat.ceil (Real.exp (348 / (1000 * δ16))) ≤ q)
      linarith
    have h4 : 348 / (1000 * δ16) ≤ Real.log (q:ℝ) := by
      rw [Real.le_log_iff_exp_le hqpos]; exact h3
    calc (348:ℝ)/1000 = δ16 * (348 / (1000 * δ16)) := by field_simp
      _ ≤ δ16 * Real.log (q:ℝ) := mul_le_mul_of_nonneg_left h4 hδ16pos.le
  have hwinρ1_16 : ‖(1:ℂ) + (ρ₁.im : ℂ) * Complex.I - ρ₁‖ ≤ δ16 := by
    have h1 : (1:ℂ) + (ρ₁.im : ℂ) * Complex.I - ρ₁ = ((1 - ρ₁.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn1, hβlam, div_le_iff₀ hlogq]
    linarith [hsmall, hδlog16]
  have hwinρ1_8 : ‖(1:ℂ) + (ρ₁.im : ℂ) * Complex.I - ρ₁‖ ≤ δ8 := by
    have h1 : (1:ℂ) + (ρ₁.im : ℂ) * Complex.I - ρ₁ = ((1 - ρ₁.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn1, hβlam, div_le_iff₀ hlogq]
    linarith [hsmall, hδlog8]
  have hγ1 : 1 < |ρ₁.im| := him1
  -- ## the case split
  by_cases hcaseI : ∀ k : ℕ, 1 ≤ k → k ≤ 4 →
      (χ₁ ^ k = 1 ∨ ((orderOf (χ₁ ^ k) : ℝ) ≤ Real.log ((((χ₁ ^ k).conductor : ℕ) : ℝ))
        ∨ (χ₁ ^ k) ^ 60 = 1))
  · -- ==================== Case I: the `1/8` supply at every slot ====================
    set β : ℝ := ρ₁.re with hβdef
    set γ : ℝ := ρ₁.im with hγdef
    have hpt1 : ((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I) = ρ₁ := by
      rw [hβdef, hγdef]
      apply Complex.ext <;> simp
    have hptL : ∀ k : ℕ, (((β:ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I).re) = β := by
      intro k; simp
    have hptI : ∀ k : ℕ, (((β:ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I).im) = (k:ℝ)*γ := by
      intro k; simp
    -- per-slot `1/8` supplies
    have hL8_at : ∀ (k : ℕ) (hk1 : 1 ≤ k) (hk4 : k ≤ 4) (hkne : χ₁ ^ k ≠ 1)
        [hc : NeZero (χ₁ ^ k).conductor],
        Commons.NumberTheory.Linnik.L52Hyp (χ₁ ^ k) ((1:ℝ)/8) (1/1000000) δ8 := by
      intro k hk1 hk4 hkne hc
      haveI : NeZero (χ₁ ^ k).conductor := ⟨(χ₁ ^ k).conductor_ne_zero⟩
      rcases hcaseI k hk1 hk4 with h1 | h2
      · exact absurd h1 hkne
      · exact hL8 q hq8 (χ₁ ^ k) hkne h2
    -- window zeros of a non-principal character lie to the left of `β`
    have hzwI : ∀ (ψ : DirichletCharacter ℂ q) [NeZero ψ.conductor], ψ ≠ 1 → ∀ {s : ℂ},
        s.re = β → |s.im| ≤ 4 * L + 1 →
        (∀ u : ℂ, (MeromorphicOn.divisor (DirichletCharacter.completedLFunction ψ.primitiveCharacter)
            (Metric.closedBall 0 (|s.im| + 2))) u ≠ 0 →
          ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ8 → u.re ≤ s.re) := by
      intro ψ _inst hψ s hsre hsim u hdiv hwin
      have hzm : Work.LinnikContract.zeroMult ψ u ≠ 0 :=
        Work.ZeroFreeTables.OffAxis.zeroMult_ne_zero_of_divisor ψ hψ hdiv
      have huim : |u.im| ≤ 10 * L := by
        have h1 : |s.im - u.im| ≤ δ8 := by
          have h3 := Complex.abs_im_le_norm ((1:ℂ) + (s.im : ℂ) * Complex.I - u)
          have h4 : (((1:ℂ) + (s.im : ℂ) * Complex.I - u).im) = s.im - u.im := by simp
          rw [h4] at h3
          exact le_trans h3 hwin
        have h2 : |u.im| ≤ |s.im| + δ8 := by
          calc |u.im| = |s.im - (s.im - u.im)| := by ring_nf
            _ ≤ |s.im| + |s.im - u.im| := abs_sub _ _
            _ ≤ |s.im| + δ8 := by linarith
        linarith [h2, hsim, hδ8lt1, hL]
      have hle := hR.2 ψ u ⟨hψ, hzm, huim⟩
      rw [hsre]
      simp only [Work.LinnikContract.lamOf] at hle
      nlinarith [hle, hlogq]
    -- A := ∫ e^{λ₁ t} f
    set A : ℝ := ∫ t in (0:ℝ)..(8/3), Real.exp (Work.LinnikContract.lamOf q ρ₁ * t) * f t
      with hAdef
    have hA_le : A ≤ (1147:ℝ)/1000 := by
      rw [hAdef, hfdef]
      exact Work.ZeroFreeTables.H4.Tf72FNegLamLe hlamnn (by linarith)
    have hb0 : Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ)) (β:ℂ) 1
        ≤ (Real.log (q:ℝ)) * (A + f 0 * (1/1000000)) := by
      have h := hKP (q := q) hqP (β := β) (lam := Work.LinnikContract.lamOf q ρ₁)
        (by rw [hβdef, Work.LinnikContract.lamOf]; ring) (by rw [hβdef]; exact hβre)
      rw [← HB94.Ksum_def_aux] at h
      rw [← hAdef] at h
      linarith only [h]
    have hb1 : Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ))
          ((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I) χ₁
        ≤ (Real.log (q:ℝ)) * (-(8:ℝ)/9 + f 0 * ((1:ℝ)/8 + 1/1000000)) := by
      have h := hKS8 (q := q) hqS8 χ₁ hχ1 (s := (β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I) (ρ := ρ₁)
        (by rw [hpt1]; exact hβre)
        (by rw [hpt1]; linarith [hγL, hLlog, hlogq])
        (by rw [hpt1]; exact hslo)
        (by
          rcases hcaseI 1 (by norm_num) (by norm_num) with h1 | h2
          · exact absurd (by simpa only [pow_one] using h1) hχ1
          · exact hL8 q hq8 χ₁ hχ1 (by simpa only [pow_one] using h2))
        (by rw [hpt1]; exact hdiv1)
        (by rw [hpt1]; exact hwinρ1_8)
        (by
          intro u hdiv hwin
          exact hzwI χ₁ hχ1 (by rw [hpt1]) (by rw [hpt1]; linarith [hγL, hL]) u hdiv hwin)
      rw [← HB94.Ksum_def_aux] at h
      have hs_eq : ((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I) - ρ₁ = 0 := by rw [hpt1, sub_self]
      rw [hs_eq] at h
      have hF0c0 : (∫ t in (0:ℝ)..((8:ℝ)/3),
          Complex.exp (-(((0:ℂ) * (Real.log (q:ℝ)) * (t:ℂ)))) * ((f t : ℝ):ℂ)).re = 8/9 := by
        have h1 : ∀ t : ℝ, Complex.exp (-(((0:ℂ) * (Real.log (q:ℝ)) * (t:ℂ))))
            * ((f t : ℝ):ℂ) = ((f t : ℝ):ℂ) := by
          intro t
          rw [zero_mul, zero_mul, neg_zero, Complex.exp_zero, one_mul]
        rw [intervalIntegral.integral_congr (fun t _ => h1 t), intervalIntegral.integral_ofReal]
        simp only [Complex.ofReal_re]
        exact hF0
      rw [hF0c0] at h
      linarith only [h]
    have hb_self_or_princ : ∀ (k : ℕ) (hk2 : 2 ≤ k) (hk4 : k ≤ 4),
        Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ)) ((β:ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I) (χ₁^k)
          ≤ (Real.log (q:ℝ)) * (f 0 * ((1:ℝ)/8 + 1/1000000)) := by
      intro k hk2 hk4
      haveI : NeZero (χ₁ ^ k).conductor := ⟨(χ₁ ^ k).conductor_ne_zero⟩
      by_cases hk : χ₁ ^ k = 1
      · have hτ1 : 1 ≤ |(k:ℝ)*γ| := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
          have hk2' : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
          have hγabs : |γ| = |ρ₁.im| := by rw [hγdef]
          nlinarith only [hγabs, him1, hk2', abs_nonneg γ]
        have hτ10 : |(k:ℝ)*γ| ≤ 10 * (Real.log (q:ℝ)) := by
          rw [abs_mul, abs_of_nonneg (by positivity)]
          have hk4' : (k:ℝ) ≤ 4 := by exact_mod_cast hk4
          have hγabs : |γ| ≤ L := by rw [hγdef]; exact hγL
          nlinarith only [mul_le_mul hk4' hγabs (abs_nonneg γ) (by norm_num : (0:ℝ) ≤ 4), hLlog, hlogq]
        have h := hKPh (q := q) hqPh (β := β) (τ := (k:ℝ)*γ)
          (by rw [hβdef]; exact hβre) hτ1 hτ10
        have hpt : ((β:ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I)
            = (β:ℂ) + (((k:ℝ)*γ : ℝ) : ℂ)*Complex.I := by push_cast; ring
        rw [hpt, hk]
        refine le_trans h ?_
        have h1 : (1:ℝ)/1000000 ≤ f 0 * ((1:ℝ)/8 + 1/1000000) := by
          rw [hf0val]; norm_num
        calc (1:ℝ)/1000000 * Real.log (q:ℝ) = Real.log (q:ℝ) * (1/1000000) := by ring
          _ ≤ Real.log (q:ℝ) * (f 0 * ((1:ℝ)/8 + 1/1000000)) :=
              mul_le_mul_of_nonneg_left h1 hlogq.le
      · have h := hKT8 (q := q) hqT8 (χ₁^k) hk (s := (β:ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I)
          (by rw [hptL k]; rw [hβdef]; exact hβre)
          (by
            rw [hptI k, abs_mul, abs_of_nonneg (by positivity)]
            have hk4' : (k:ℝ) ≤ 4 := by exact_mod_cast hk4
            have hγabs : |γ| ≤ L := by rw [hγdef]; exact hγL
            nlinarith only [mul_le_mul hk4' hγabs (abs_nonneg γ) (by norm_num : (0:ℝ) ≤ 4), hLlog, hlogq])
          (by rw [hptL k]; rw [hβdef]; exact hslo)
          (hL8_at k (by omega) hk4 hk)
          (by
            intro u hdiv hwin
            exact hzwI (χ₁^k) hk (by rw [hptL k])
              (by
                rw [hptI k, abs_mul, abs_of_nonneg (by positivity)]
                have hk4' : (k:ℝ) ≤ 4 := by exact_mod_cast hk4
                have hγabs : |γ| ≤ L := by rw [hγdef]; exact hγL
                nlinarith only [mul_le_mul hk4' hγabs (abs_nonneg γ) (by norm_num : (0:ℝ) ≤ 4), hL]) u hdiv hwin)
        rw [← HB94.Ksum_def_aux] at h
        linarith only [h]
    -- the (9.15) combination
    have hexp : (∑ k ∈ Finset.range 5, Work.ZeroFreeTables.c95 k *
        Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ)) ((β : ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I) (χ₁^k))
        = (14379:ℝ) * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ)) ((β:ℂ)) 1
        + 24480 * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ))
            ((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I) χ₁
        + 14900 * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ))
            ((β:ℂ) + ((2:ℝ)*γ : ℂ)*Complex.I) (χ₁^2)
        + 6000 * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ))
            ((β:ℂ) + ((3:ℝ)*γ : ℂ)*Complex.I) (χ₁^3)
        + 1250 * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ))
            ((β:ℂ) + ((4:ℝ)*γ : ℂ)*Complex.I) (χ₁^4) := by
      norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Work.ZeroFreeTables.c95,
        pow_zero, pow_one]
    have hcomb : 0 ≤ (14379:ℝ) * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ)) ((β:ℂ)) 1
        + 24480 * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ))
            ((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I) χ₁
        + 14900 * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ))
            ((β:ℂ) + ((2:ℝ)*γ : ℂ)*Complex.I) (χ₁^2)
        + 6000 * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ))
            ((β:ℂ) + ((3:ℝ)*γ : ℂ)*Complex.I) (χ₁^3)
        + 1250 * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ))
            ((β:ℂ) + ((4:ℝ)*γ : ℂ)*Complex.I) (χ₁^4) := by
      have h := ksum_trigPoly_nonneg (q := q) (f := f) hfnn (x₀ := (8:ℝ)/3)
        (L := Real.log (q:ℝ)) (β := β) (γ := γ) hlogq (by norm_num) hfsupp
        (c := Work.ZeroFreeTables.c95) (d := 4) Work.ZeroFreeTables.c95_hP χ₁
      rw [hexp] at h
      exact h
    have hbr : (14379:ℝ) * (A + f 0 * (1/1000000))
        + 24480 * (-(8:ℝ)/9 + f 0 * ((1:ℝ)/8 + 1/1000000))
        + 14900 * (f 0 * ((1:ℝ)/8 + 1/1000000))
        + 6000 * (f 0 * ((1:ℝ)/8 + 1/1000000))
        + 1250 * (f 0 * ((1:ℝ)/8 + 1/1000000)) < 0 := by
      rw [hf0val]
      linarith only [hA_le]
    exact contrab5 hlogq hcomb hb0 hb1 (hb_self_or_princ 2 (by norm_num) (by norm_num))
      (hb_self_or_princ 3 (by norm_num) (by norm_num))
      (hb_self_or_princ 4 (by norm_num) (by norm_num)) hbr
  · -- ==================== Case II: the `1/6` supply, `λ* = λ₁ + 472/1000` ====================
    push Not at hcaseI
    obtain ⟨k0, hk01, hk04, hkA, hkB⟩ := hcaseI
    have h60 : ¬ (orderOf χ₁ ∣ 60) := by
      intro hdvd
      have h1 : χ₁ ^ 60 = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd
      have h2 : (χ₁ ^ k0) ^ 60 = 1 := by
        rw [← pow_mul, Nat.mul_comm k0 60, pow_mul, h1, one_pow]
      exact hkB.2 h2
    have hne2 : χ₁ ^ 2 ≠ 1 := fun h =>
      h60 (dvd_trans (orderOf_dvd_iff_pow_eq_one.mpr h) (by norm_num))
    have hpow_ne : ∀ k : ℕ, 2 ≤ k → k ≤ 4 → χ₁ ^ k ≠ 1 := by
      intro k hk2 hk4 h1
      have hd : orderOf χ₁ ∣ k := orderOf_dvd_iff_pow_eq_one.mpr h1
      have hk60 : k ∣ 60 := by interval_cases k <;> norm_num
      exact h60 (dvd_trans hd hk60)
    have hpow_ne_self : ∀ k : ℕ, 2 ≤ k → k ≤ 4 → χ₁ ^ k ≠ χ₁ := by
      intro k hk2 hk4 h
      have h1 : χ₁ ^ (k-1) = 1 := by
        have h3 : χ₁ ^ k = χ₁ ^ (k-1) * χ₁ := by
          rw [← pow_succ]; congr 1; omega
        have h4 : χ₁ ^ (k-1) * χ₁ = χ₁ := by rw [← h3]; exact h
        have h5 : χ₁ ^ (k-1) * χ₁ = 1 * χ₁ := by rw [h4, one_mul]
        exact mul_right_cancel h5
      have hd : orderOf χ₁ ∣ k - 1 := orderOf_dvd_iff_pow_eq_one.mpr h1
      have hk60 : k - 1 ∣ 60 := by interval_cases k <;> norm_num
      exact h60 (dvd_trans hd hk60)
    have hpow_ne_inv : ∀ k : ℕ, 2 ≤ k → k ≤ 4 → χ₁ ^ k ≠ χ₁⁻¹ := by
      intro k hk2 hk4 h
      have h1 : χ₁ ^ (k+1) = 1 := by
        rw [pow_succ, h]
        exact inv_mul_cancel χ₁
      have hd : orderOf χ₁ ∣ k + 1 := orderOf_dvd_iff_pow_eq_one.mpr h1
      have hk60 : k + 1 ∣ 60 := by interval_cases k <;> norm_num
      exact h60 (dvd_trans hd hk60)
    -- ## the base point `β = 1 - (λ₁ + 472/1000)/log q`
    set ls : ℝ := Work.LinnikContract.lamOf q ρ₁ + (472:ℝ)/1000 with hlsdef
    set β : ℝ := 1 - ls / Real.log (q:ℝ) with hβdef
    set γ : ℝ := ρ₁.im with hγdef
    have hls_le : ls ≤ (82:ℝ)/100 := by rw [hlsdef]; linarith
    have hls_nn : 0 ≤ ls := by rw [hlsdef]; linarith
    have hptL : ∀ k : ℕ, (((β:ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I).re) = β := by
      intro k; simp
    have hptI : ∀ k : ℕ, (((β:ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I).im) = (k:ℝ)*γ := by
      intro k; simp
    have hptL1 : (((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I).re) = β := by simp
    have hptI1 : (((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I).im) = (1:ℝ)*γ := by simp
    have hβ1 : |β - 1| ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) := by
      have h2 : |β - 1| = ls / Real.log (q:ℝ) := by
        rw [hβdef]
        have h3 : (1:ℝ) - ls / Real.log (q:ℝ) - 1 = -(ls / Real.log (q:ℝ)) := by ring
        rw [h3, abs_neg, abs_of_nonneg (div_nonneg hls_nn hlogq.le)]
      rw [h2]
      exact div_le_div_of_nonneg_right (le_trans hls_le hsqrtge82) hlogq.le
    have hβslo : 1 - Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) ≤ β := by
      have h : ls / Real.log (q:ℝ)
          ≤ Real.sqrt (Real.log (Real.log (q:ℝ))) / Real.log (q:ℝ) :=
        div_le_div_of_nonneg_right (le_trans hls_le hsqrtge82) hlogq.le
      rw [hβdef]
      linarith
    -- the kept zero `ρ₁` sits at distance `472/1000` in `λ` to the right of `β`
    have hs_eq : ((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I) - ρ₁ = ((β - ρ₁.re : ℝ) : ℂ) := by
      apply Complex.ext
      · have hre : (((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I) - ρ₁).re = β - ρ₁.re := by simp
        rw [hre]; simp
      · have him : (((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I) - ρ₁).im = (1:ℝ)*γ - ρ₁.im := by simp
        rw [him, hγdef]; simp
    have hβsub : β - ρ₁.re = -(472:ℝ)/1000 / Real.log (q:ℝ) := by
      rw [hβdef, hlsdef]
      have h1 : (1:ℝ) - (Work.LinnikContract.lamOf q ρ₁ + 472/1000) / Real.log (q:ℝ) - ρ₁.re
          = (1 - ρ₁.re) - (Work.LinnikContract.lamOf q ρ₁ + 472/1000) / Real.log (q:ℝ) := by ring
      rw [h1, hβlam]
      field_simp
      ring
    have hdiff : ((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I) - ρ₁
        = (((-(472:ℝ)/1000) / Real.log (q:ℝ) : ℝ) : ℂ) := by
      rw [hs_eq, hβsub]
    have hz : (((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I) - ρ₁) * (Real.log (q:ℝ))
        = (((-(472:ℝ)/1000) : ℝ) : ℂ) := by
      rw [hdiff, ← Complex.ofReal_mul]
      congr 1
      rw [div_mul_cancel₀]
      exact hlogq.ne'
    have hFval : (∫ t in (0:ℝ)..(8:ℝ)/3,
        Complex.exp (-((((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I) - ρ₁) * (Real.log (q:ℝ)) * (t:ℂ)))
          * ((f t : ℝ):ℂ)).re
        = ∫ t in (0:ℝ)..(8:ℝ)/3, Real.exp ((472:ℝ)/1000 * t) * f t := by
      rw [hz, hfdef]
      have h := Fw_eq_expint (z := (((-(472:ℝ)/1000) : ℝ) : ℂ)) (by simp)
      rw [h]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      have h3 : -(((↑(-(472:ℝ)/1000) : ℂ)).re * t) = (472:ℝ)/1000 * t := by
        simp
        ring
      rw [h3]
    have hFge : (1260:ℝ)/1000 ≤ (∫ t in (0:ℝ)..(8:ℝ)/3,
        Complex.exp (-((((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I) - ρ₁) * (Real.log (q:ℝ)) * (t:ℂ)))
          * ((f t : ℝ):ℂ)).re := by
      rw [hFval, hfdef]
      exact RectC.Numeric95b.2
    have hFnn : 0 ≤ (∫ t in (0:ℝ)..(8:ℝ)/3,
        Complex.exp (-((((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I) - ρ₁) * (Real.log (q:ℝ)) * (t:ℂ)))
          * ((f t : ℝ):ℂ)).re := by
      rw [hFval]
      exact intervalIntegral.integral_nonneg (by norm_num)
        (fun t _ => mul_nonneg (Real.exp_nonneg _) (hfnn t))
    have hdiv1' : (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ₁.primitiveCharacter)
        (Metric.closedBall 0 (|(((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I)).im| + 2))) ρ₁ ≠ 0 := by
      rw [hptI1]
      have h3 : |(1:ℝ)*γ| = |ρ₁.im| := by
        rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (1:ℝ) by norm_num), one_mul, hγdef]
      rw [h3]
      exact hdiv1
    have hwin1' : ‖(1:ℂ) + ((((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I)).im : ℂ) * Complex.I - ρ₁‖ ≤ δ16 := by
      rw [hptI1]
      have h3 : (1:ℝ)*γ = ρ₁.im := by rw [one_mul, hγdef]
      rw [h3]
      exact hwinρ1_16
    -- ## the five bounds
    have hb0 : Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ)) (β:ℂ) 1
        ≤ (Real.log (q:ℝ)) * ((1710:ℝ)/1000 + f 0 * (1/1000000)) := by
      have hlam : ls = Real.log (q:ℝ) * (1 - β) := by
        rw [hβdef]
        field_simp
        ring
      have h := hKP (q := q) hqP (β := β) (lam := ls) hlam (by rw [hβdef]; exact hβ1)
      rw [← HB94.Ksum_def_aux] at h
      have hA : (∫ t in (0:ℝ)..(8:ℝ)/3, Real.exp (ls * t) * f t) ≤ (1710:ℝ)/1000 := by
        have h2 : (∫ t in (0:ℝ)..(8:ℝ)/3, Real.exp (ls * t) * f t)
            ≤ ∫ t in (0:ℝ)..(8:ℝ)/3, Real.exp ((82:ℝ)/100 * t) * f t := by
          have h3 := Work.ZeroFreeTables.OffAxis.expint_mono (a := ls) (b := (82:ℝ)/100)
            (by linarith [hls_le])
          rw [← hfdef] at h3
          exact h3
        have h4 : (∫ t in (0:ℝ)..(8:ℝ)/3, Real.exp ((82:ℝ)/100 * t) * f t)
            ≤ (1710:ℝ)/1000 := by
          rw [hfdef]
          exact RectC.Numeric95b.1
        linarith
      have h5 : (Real.log (q:ℝ)) * (∫ t in (0:ℝ)..(8:ℝ)/3, Real.exp (ls * t) * f t)
            + f 0 * (1/1000000) * Real.log (q:ℝ)
          ≤ (Real.log (q:ℝ)) * ((1710:ℝ)/1000 + f 0 * (1/1000000)) := by
        nlinarith only [mul_le_mul_of_nonneg_left hA hlogq.le]
      linarith only [h, h5]
    have hb1 : Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ))
          ((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I) χ₁
        ≤ (Real.log (q:ℝ)) * (-(1260:ℝ)/1000 + f 0 * ((1:ℝ)/6 + 1/1000000)) := by
      have h := hKS16 (q := q) hqS16 χ₁ hχ1 (s := (β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I) (ρ := ρ₁)
        (by rw [hptL1]; exact hβ1)
        (by
          rw [hptI1]
          have h3 : |(1:ℝ)*γ| ≤ L := by
            rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (1:ℝ) by norm_num), one_mul]
            rw [hγdef]; exact hγL
          linarith [h3, hLlog, hlogq])
        (by rw [hptL1]; exact hβslo)
        (by simpa only [pow_one] using h16raw q hq16 χ₁ hχ1)
        hdiv1'
        hwin1'
        hFnn
        (by
          intro u hdiv hwin hne
          have hzm : Work.LinnikContract.zeroMult χ₁ u ≠ 0 :=
            Work.ZeroFreeTables.OffAxis.zeroMult_ne_zero_of_divisor χ₁ hχ1 hdiv
          have huim : |u.im| ≤ 2 * L := by
            have h1 : |(((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I)).im - u.im| ≤ δ16 := by
              have h3 := Complex.abs_im_le_norm
                ((1:ℂ) + ((((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I)).im : ℂ) * Complex.I - u)
              have h4 : (((1:ℂ) + ((((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I)).im : ℂ) * Complex.I - u).im)
                  = (((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I)).im - u.im := by simp
              rw [h4] at h3
              exact le_trans h3 hwin
            have h2 : |u.im| ≤ |(((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I)).im| + δ16 := by
              calc |u.im| = |(((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I)).im
                    - ((((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I)).im - u.im)| := by ring_nf
                _ ≤ |(((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I)).im|
                    + |(((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I)).im - u.im| := abs_sub _ _
                _ ≤ |(((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I)).im| + δ16 := by linarith
            rw [hptI1] at h2
            have h3 : |(1:ℝ)*γ| ≤ L := by
              rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (1:ℝ) by norm_num), one_mul]
              rw [hγdef]; exact hγL
            linarith [h2, h3, hδ16lt1, hL]
          have hlamu := hSelf q hqSelf χ₁ ρ₁ hR hne2 hsmall u hzm huim hne
          rw [hptL1]
          simp only [Work.LinnikContract.lamOf] at hlamu
          have h3 : ls ≤ (1 - u.re) * Real.log (q:ℝ) := by linarith [hlamu, hls_le]
          have h4 : ls / Real.log (q:ℝ) ≤ 1 - u.re := by
            rw [div_le_iff₀ hlogq]
            exact h3
          rw [hβdef]
          linarith)
      rw [← HB94.Ksum_def_aux] at h
      refine le_trans h ?_
      have h6 : -(Real.log (q:ℝ)) * (∫ t in (0:ℝ)..(8:ℝ)/3,
            Complex.exp (-((((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I) - ρ₁) * (Real.log (q:ℝ)) * (t:ℂ)))
              * ((f t : ℝ):ℂ)).re
          ≤ -(Real.log (q:ℝ)) * ((1260:ℝ)/1000) :=
        mul_le_mul_of_nonpos_left hFge (by linarith [hlogq])
      linarith only [h, h6]
    have hb_self : ∀ (k : ℕ) (hk2 : 2 ≤ k) (hk4 : k ≤ 4),
        Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ)) ((β:ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I) (χ₁^k)
          ≤ (Real.log (q:ℝ)) * (f 0 * ((1:ℝ)/6 + 1/1000000)) := by
      intro k hk2 hk4
      haveI : NeZero (χ₁ ^ k).conductor := ⟨(χ₁ ^ k).conductor_ne_zero⟩
      have h := hKT16 (q := q) hqT16 (χ₁^k) (hpow_ne k hk2 hk4)
        (s := (β:ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I)
        (by rw [hptL k]; exact hβ1)
        (by
          rw [hptI k]
          have h3 : |(k:ℝ)*γ| ≤ 4 * L := by
            rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (k:ℝ) by positivity)]
            have hk4' : (k:ℝ) ≤ 4 := by exact_mod_cast hk4
            have hγabs : |γ| ≤ L := by rw [hγdef]; exact hγL
            nlinarith only [mul_le_mul hk4' hγabs (abs_nonneg γ) (by norm_num : (0:ℝ) ≤ 4), hLlog, hlogq]
          linarith [h3, hLlog, hlogq])
        (by rw [hptL k]; exact hβslo)
        (h16raw q hq16 (χ₁^k) (hpow_ne k hk2 hk4))
        (by
          intro u hdiv hwin
          have hzm : Work.LinnikContract.zeroMult (χ₁^k) u ≠ 0 :=
            Work.ZeroFreeTables.OffAxis.zeroMult_ne_zero_of_divisor (χ₁^k) (hpow_ne k hk2 hk4) hdiv
          have huim : |u.im| ≤ 5 * L := by
            have h1 : |(((β:ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I)).im - u.im| ≤ δ16 := by
              have h3 := Complex.abs_im_le_norm
                ((1:ℂ) + ((((β:ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I)).im : ℂ) * Complex.I - u)
              have h4 : (((1:ℂ) + ((((β:ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I)).im : ℂ) * Complex.I - u).im)
                  = (((β:ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I)).im - u.im := by simp
              rw [h4] at h3
              exact le_trans h3 hwin
            have h2 : |u.im| ≤ |(((β:ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I)).im| + δ16 := by
              calc |u.im| = |(((β:ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I)).im
                    - ((((β:ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I)).im - u.im)| := by ring_nf
                _ ≤ |(((β:ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I)).im|
                    + |(((β:ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I)).im - u.im| := abs_sub _ _
                _ ≤ |(((β:ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I)).im| + δ16 := by linarith
            rw [hptI k] at h2
            have h3 : |(k:ℝ)*γ| ≤ 4 * L := by
              rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ (k:ℝ) by positivity)]
              have hk4' : (k:ℝ) ≤ 4 := by exact_mod_cast hk4
              have hγabs : |γ| ≤ L := by rw [hγdef]; exact hγL
              nlinarith only [mul_le_mul hk4' hγabs (abs_nonneg γ) (by norm_num : (0:ℝ) ≤ 4), hLlog, hlogq]
            linarith [h2, h3, hδ16lt1, hL]
          have hlamu := hsecond q hqsec χ₁ ρ₁ hR hsmall him1 (χ₁^k) u (hpow_ne k hk2 hk4) hzm
            (hpow_ne_self k hk2 hk4) (hpow_ne_inv k hk2 hk4) huim
          rw [hptL k]
          simp only [Work.LinnikContract.lamOf] at hlamu
          have h3 : ls ≤ (1 - u.re) * Real.log (q:ℝ) := by
            rw [hlsdef]
            simp only [Work.LinnikContract.lamOf]
            linarith [hlamu]
          have h4 : ls / Real.log (q:ℝ) ≤ 1 - u.re := by
            rw [div_le_iff₀ hlogq]
            exact h3
          rw [hβdef]
          linarith)
      rw [← HB94.Ksum_def_aux] at h
      linarith only [h]
    -- ## the (9.15) combination
    have hexp : (∑ k ∈ Finset.range 5, Work.ZeroFreeTables.c95 k *
        Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ)) ((β : ℂ) + ((k:ℝ)*γ : ℂ)*Complex.I) (χ₁^k))
        = (14379:ℝ) * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ)) ((β:ℂ)) 1
        + 24480 * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ))
            ((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I) χ₁
        + 14900 * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ))
            ((β:ℂ) + ((2:ℝ)*γ : ℂ)*Complex.I) (χ₁^2)
        + 6000 * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ))
            ((β:ℂ) + ((3:ℝ)*γ : ℂ)*Complex.I) (χ₁^3)
        + 1250 * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ))
            ((β:ℂ) + ((4:ℝ)*γ : ℂ)*Complex.I) (χ₁^4) := by
      norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Work.ZeroFreeTables.c95,
        pow_zero, pow_one]
    have hcomb : 0 ≤ (14379:ℝ) * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ)) ((β:ℂ)) 1
        + 24480 * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ))
            ((β:ℂ) + ((1:ℝ)*γ : ℂ)*Complex.I) χ₁
        + 14900 * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ))
            ((β:ℂ) + ((2:ℝ)*γ : ℂ)*Complex.I) (χ₁^2)
        + 6000 * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ))
            ((β:ℂ) + ((3:ℝ)*γ : ℂ)*Complex.I) (χ₁^3)
        + 1250 * Work.ZeroFreeTables.Ksum q f (Real.log (q:ℝ))
            ((β:ℂ) + ((4:ℝ)*γ : ℂ)*Complex.I) (χ₁^4) := by
      have h := ksum_trigPoly_nonneg (q := q) (f := f) hfnn (x₀ := (8:ℝ)/3)
        (L := Real.log (q:ℝ)) (β := β) (γ := γ) hlogq (by norm_num) hfsupp
        (c := Work.ZeroFreeTables.c95) (d := 4) Work.ZeroFreeTables.c95_hP χ₁
      rw [hexp] at h
      exact h
    have hbr : (14379:ℝ) * ((1710:ℝ)/1000 + f 0 * (1/1000000))
        + 24480 * (-(1260:ℝ)/1000 + f 0 * ((1:ℝ)/6 + 1/1000000))
        + 14900 * (f 0 * ((1:ℝ)/6 + 1/1000000))
        + 6000 * (f 0 * ((1:ℝ)/6 + 1/1000000))
        + 1250 * (f 0 * ((1:ℝ)/6 + 1/1000000)) < 0 := by
      rw [hf0val]
      norm_num
    exact contrab5 hlogq hcomb hb0 hb1 (hb_self 2 (by norm_num) (by norm_num))
      (hb_self 3 (by norm_num) (by norm_num))
      (hb_self 4 (by norm_num) (by norm_num)) hbr

end Work.ZeroFreeTables.OffAxis
