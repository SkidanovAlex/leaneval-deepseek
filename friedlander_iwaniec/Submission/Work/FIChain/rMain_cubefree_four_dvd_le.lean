import Mathlib
import Submission.Work.FIChain.Defs
import Submission.ASP.S40
import Submission.ASP.S31
import Submission.ASP.S22
import Submission.ASP.S21
import Submission.ASP.S35
import Submission.ASP.S36
import Submission.ASP.S34
import Submission.ASP.S33
import Submission.ASP.S32
import Submission.ASP.S9b
import Submission.ASP.S9d
import Submission.ASP.S37
import Submission.ASP_R3

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The modulus exponent `141/200`; the arithmetic of the argument is driven by
`141/800 + 9/16 + 1/100 = 599/800 < 3/4`. -/
local notation "Dmax" => ((141 : ℝ) / 200)

/-- The `CubefreeD`-filtered range is definitionally the expanded filter used by
`Submission.ASP.four_dvd_sum_le`. -/
private lemma four_dvd_filter_eq (N : ℕ) :
    (Finset.range N).filter (fun d => Submission.CubefreeD d ∧ 4 ∣ d)
      = (Finset.range N).filter
          (fun d => (∀ p ∈ d.primeFactors, d.factorization p ≤ 2) ∧ 4 ∣ d) := rfl

theorem rMain_cubefree_four_dvd_le (lamm : ℝ) : ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
    ∀ N : ℕ, 3 ≤ N → (N : ℝ) ≤ (x : ℝ) ^ ((141 : ℝ) / 200) →
    (∑ k ∈ (Finset.range N).filter (fun d => Submission.CubefreeD d ∧ 4 ∣ d),
        |(Submission.Ad k t : ℝ) - (Submission.gdens k : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ (Submission.Aseq x : ℝ) * (Real.log (x : ℝ)) ^ (-lamm) := by
  obtain ⟨CAd, hCAd, hAd⟩ := Submission.X2Y4R.Ad_sub_Md_sum_le
  obtain ⟨CMd, hCMd, hMd⟩ := Submission.Md_sub_main_term_sum_le
  obtain ⟨CM4, hCM4, hM4⟩ := Submission.Md_cubefree_asymptotic_uniform
  obtain ⟨Cg, Ag, hCg, hGg⟩ := Submission.X2Y4R.cubeSum_gdens_le
  obtain ⟨Ch, Ah, hCh, hHh⟩ := Submission.X2Y4R.cubeSum_hdens_le
  obtain ⟨Cinv, hCinv, hInv⟩ := Commons.NumberTheory.Diophantine.sum_inv_sqrt_asymptotic
  obtain ⟨Ct, hCt, hTau⟩ := Commons.NumberTheory.Divisors.sum_tau_pow_div_le 2
  obtain ⟨CAs, hCAs, hAs⟩ := Submission.Aseq_asymptotic
  obtain ⟨CAd2, hCAd2, hAd2⟩ := Submission.X2Y4R.sum_Ad_le
  obtain ⟨CAu, hCAu, hAu⟩ := Submission.X2Y4R.Aseq_le_const_mul_rpow
  obtain ⟨cAl, hcAl, XAl, hAl⟩ := Submission.X2Y4R.exists_const_mul_rpow_le_Aseq
  have hAh3 : ∀ y : ℕ, 3 ≤ y → Submission.X2Y4R.cubeSum y
      (fun a b => (Submission.hdens a b : ℝ)) ≤ Ch * (Real.log y) ^ Ah :=
    fun y hy => hHh y (by omega)
  have hAg3 : ∀ y : ℕ, 3 ≤ y → Submission.X2Y4R.cubeSum y
      (fun a b => |(Submission.gdens (a * b ^ 2) : ℝ)|) ≤ Cg * (Real.log y) ^ Ag :=
    fun y hy => hGg y (by omega)
  have hκ0 : (0 : ℝ) ≤ ∫ u in (0)..1, Real.sqrt (1 - u ^ 4) :=
    intervalIntegral.integral_nonneg (by norm_num) (fun u _ => Real.sqrt_nonneg _)
  -- ### the auxiliary constants
  set Ahh : ℝ := max Ah 0 with hAhhdef
  set Agg : ℝ := max Ag 0 with hAggdef
  have hAhh0 : 0 ≤ Ahh := by rw [hAhhdef]; exact le_max_right _ _
  have hAgg0 : 0 ≤ Agg := by rw [hAggdef]; exact le_max_right _ _
  have hAhh : Ah ≤ Ahh := by rw [hAhhdef]; exact le_max_left _ _
  have hAgg : Ag ≤ Agg := by rw [hAggdef]; exact le_max_left _ _
  set M : ℝ := Ahh + Agg + 10 with hMdef
  have hAhM : Ah ≤ M := by rw [hMdef]; linarith [hAhh]
  have hAgM : Ag ≤ M := by rw [hMdef]; linarith [hAgg]
  have hM1 : (1 : ℝ) ≤ M := by rw [hMdef]; linarith [hAhh0, hAgg0]
  have hM0 : (0 : ℝ) ≤ M := le_trans zero_le_one hM1
  set K4 : ℝ := (2 : ℝ) ^ M + 1 with hK4def
  have hK41 : (1 : ℝ) ≤ K4 := by
    rw [hK4def]
    linarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) M]
  have hK40 : (0 : ℝ) < K4 := lt_of_lt_of_le zero_lt_one hK41
  set c1 : ℝ := cAl / 16 with hc1def
  have hc1 : 0 < c1 := by rw [hc1def]; positivity
  have hc10 : 0 ≤ c1 := le_of_lt hc1
  set KK : ℝ := 2 * CM4 * Ch + 32 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * Cg + CAs * Cg
    with hKKdef
  have hKKpos : 0 < KK := by
    rw [hKKdef]
    have h1 : 0 < 2 * CM4 * Ch := by positivity
    have h2 : 0 ≤ 32 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * Cg :=
      mul_nonneg (mul_nonneg (by norm_num) hκ0) hCg.le
    have h3 : 0 ≤ CAs * Cg := mul_nonneg hCAs.le hCg.le
    linarith
  have hKK0 : 0 ≤ KK := le_of_lt hKKpos
  -- ### the polylogarithmic thresholds
  obtain ⟨Z1, hZ1x, hZ1⟩ := Submission.X2Y4R3.poly_tail_gen CAd
    (Dmax * ((1 : ℝ) / 4) + ((9 : ℝ) / 16 + 1 / 100)) 0 c1 lamm hCAd (by norm_num) hc1
  obtain ⟨Z2, hZ2x, hZ2⟩ := Submission.X2Y4R3.poly_tail_gen (CMd * 64) ((1 : ℝ) / 4) 6 c1
    lamm (by positivity) (by norm_num) hc1
  obtain ⟨Z3, hZ3x, hZ3⟩ := Submission.X2Y4R3.poly_tail_gen 16 (Dmax * ((1 : ℝ) / 2)) 0 c1
    lamm (by norm_num) (by norm_num) hc1
  obtain ⟨Z4, hZ4x, hZ4⟩ := Submission.X2Y4R3.poly_tail_gen (8 * Cinv) 0 0 c1 lamm
    (by positivity) (by norm_num) hc1
  obtain ⟨Z5, hZ5x, hZ5⟩ := Submission.X2Y4R3.poly_tail_gen (256 * Ct) ((1 : ℝ) / 4) 4 (c1 / 2)
    lamm (by positivity) (by norm_num) (by positivity)
  obtain ⟨Z6, hZ6x, hZ6⟩ := Submission.X2Y4R3.poly_tail_gen (256 * Ct) 0 4 (c1 / 2)
    lamm (by positivity) (by norm_num) (by positivity)
  obtain ⟨Z7, hZ7x, hZ7⟩ := Submission.X2Y4R3.poly_tail_gen (KK * K4) ((1 : ℝ) / 2) M c1 lamm
    (by positivity) (by norm_num) hc1
  obtain ⟨Z8, hZ8x, hZ8⟩ := Submission.X2Y4R3.poly_tail_gen (KK * K4) 0 M c1 lamm
    (by positivity) (by norm_num) hc1
  obtain ⟨Z9, hZ9x, hZ9⟩ := Submission.X2Y4R3.poly_tail_gen 1 0 0 c1 lamm
    (by norm_num) (by norm_num) hc1
  obtain ⟨Z10, hZ10x, hZ10⟩ := Submission.X2Y4R3.poly_tail_gen 1 Dmax 0 c1 lamm
    (by norm_num) (by norm_num) hc1
  obtain ⟨Z11, hZ11x, hZ11⟩ := Submission.X2Y4R3.poly_tail_gen (2 * CAd2 * CAu) (Dmax + 1 / 100) 0
    c1 lamm (by positivity) (by norm_num) hc1
  obtain ⟨Z12, hZ12x, hZ12⟩ := Submission.X2Y4R3.poly_tail_gen (2 * CAu * Cg * K4) Dmax Agg c1
    lamm (by positivity) (by norm_num) hc1
  refine ⟨Z1 + Z2 + Z3 + Z4 + Z5 + Z6 + Z7 + Z8 + Z9 + Z10 + Z11 + Z12 + XAl + 100,
    fun x hx t ht2 htx N hN3le hNx => ?_⟩
  have hxZ1 : Z1 ≤ x := by omega
  have hxZ2 : Z2 ≤ x := by omega
  have hxZ3 : Z3 ≤ x := by omega
  have hxZ4 : Z4 ≤ x := by omega
  have hxZ5 : Z5 ≤ x := by omega
  have hxZ6 : Z6 ≤ x := by omega
  have hxZ7 : Z7 ≤ x := by omega
  have hxZ8 : Z8 ≤ x := by omega
  have hxZ9 : Z9 ≤ x := by omega
  have hxZ10 : Z10 ≤ x := by omega
  have hxZ11 : Z11 ≤ x := by omega
  have hxZ12 : Z12 ≤ x := by omega
  have hxXAl : XAl ≤ x := by omega
  have hx100 : 100 ≤ x := by omega
  have hx3 : 3 ≤ x := by omega
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by linarith
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log x := by
    have h3 : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
    have hexp : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hlog0 : (0 : ℝ) ≤ Real.log x := le_trans zero_le_one hlog1
  have hlogpos : (0 : ℝ) < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  have htle : (t : ℝ) ≤ (x : ℝ) := by exact_mod_cast htx
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (by omega : 1 ≤ t)
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := by linarith
  have htpos : (0 : ℝ) < (t : ℝ) := by linarith
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNle : (N : ℝ) ≤ (x : ℝ) := by
    have h1 : (x : ℝ) ^ Dmax ≤ (x : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [Real.rpow_one] at h1
    linarith [hNx, h1]
  have hlogN0 : (0 : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hlogN1 : (1 : ℝ) ≤ Real.log (N : ℝ) := by
    have h3 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3le
    have hexp : Real.exp 1 ≤ (N : ℝ) := by linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hlogN_le : Real.log (N : ℝ) ≤ Real.log (x : ℝ) := Real.log_le_log hNpos hNle
  have hlogNp2 : Real.log ((N : ℝ) + 2) ≤ 2 * Real.log x := by
    have h1 : (N : ℝ) + 2 ≤ 3 * (x : ℝ) := by linarith
    have h2 : Real.log ((N : ℝ) + 2) ≤ Real.log (3 * (x : ℝ)) :=
      Real.log_le_log (by linarith) h1
    have h3 : Real.log (3 * (x : ℝ)) = Real.log 3 + Real.log x :=
      Real.log_mul (by norm_num) (ne_of_gt hxpos)
    have h4 : Real.log 3 ≤ Real.log x := Real.log_le_log (by norm_num) (by exact_mod_cast hx3)
    rw [h3] at h2
    linarith
  have hlog2N2 : Real.log (2 * (N : ℝ) + 2) ≤ 2 * Real.log x := by
    have h1 : 2 * (N : ℝ) + 2 ≤ 4 * (x : ℝ) := by linarith
    have h2 : Real.log (2 * (N : ℝ) + 2) ≤ Real.log (4 * (x : ℝ)) :=
      Real.log_le_log (by linarith) h1
    have h3 : Real.log (4 * (x : ℝ)) = Real.log 4 + Real.log x :=
      Real.log_mul (by norm_num) (ne_of_gt hxpos)
    have h4 : Real.log 4 ≤ Real.log x :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 4 ≤ x))
    rw [h3] at h2
    linarith
  have hN12 : (N : ℝ) ^ ((1 : ℝ) / 4) ≤ (x : ℝ) ^ (Dmax * ((1 : ℝ) / 4)) := by
    have h1 : (N : ℝ) ^ ((1 : ℝ) / 4) ≤ ((x : ℝ) ^ Dmax) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow hN0 hNx (by norm_num)
    rwa [← Real.rpow_mul hx0] at h1
  have hsqrtN : Real.sqrt (N : ℝ) ≤ (x : ℝ) ^ (Dmax * ((1 : ℝ) / 2)) := by
    rw [Real.sqrt_eq_rpow]
    have h1 : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ ((x : ℝ) ^ Dmax) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow hN0 hNx (by norm_num)
    rwa [← Real.rpow_mul hx0] at h1
  have hlogNM : (Real.log (N : ℝ)) ^ M ≤ K4 * (Real.log x) ^ M := by
    have h1 : (Real.log (N : ℝ)) ^ M ≤ (Real.log x) ^ M :=
      Real.rpow_le_rpow hlogN0 hlogN_le hM0
    have h2 : (Real.log x) ^ M ≤ K4 * (Real.log x) ^ M :=
      le_mul_of_one_le_left (Real.rpow_nonneg hlog0 _) hK41
    linarith
  have hlogAg : (Real.log (N : ℝ)) ^ Ag ≤ K4 * (Real.log x) ^ Agg := by
    have h1 : (Real.log (N : ℝ)) ^ Ag ≤ (Real.log (N : ℝ)) ^ Agg :=
      Real.rpow_le_rpow_of_exponent_le hlogN1 hAgg
    have h2 : (Real.log (N : ℝ)) ^ Agg ≤ (Real.log x) ^ Agg :=
      Real.rpow_le_rpow hlogN0 hlogN_le hAgg0
    have h3 : (Real.log x) ^ Agg ≤ K4 * (Real.log x) ^ Agg :=
      le_mul_of_one_le_left (Real.rpow_nonneg hlog0 _) hK41
    linarith
  have hAx : cAl * (x : ℝ) ^ ((3 : ℝ) / 4) ≤ (Submission.Aseq x : ℝ) := hAl x hxXAl
  have hlogz : (0 : ℝ) ≤ (Real.log x) ^ (-lamm) := Real.rpow_nonneg hlog0 _
  have hX0 : (0 : ℝ) ≤ c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) :=
    mul_nonneg (mul_nonneg hc10 (Real.rpow_nonneg hx0 _)) (Real.rpow_nonneg hlog0 _)
  -- ### the six polylogarithmic comparisons
  have he1 : (1 : ℝ) ≤ c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by
    have h := hZ9 x hxZ9
    simpa only [Real.rpow_zero, mul_one, one_mul] using h
  have he2 : (N : ℝ) ≤ c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by
    have h := hZ10 x hxZ10
    refine le_trans hNx ?_
    simpa only [Real.rpow_zero, mul_one, one_mul] using h
  have he3 : 2 * CAd2 * CAu * (N : ℝ) * (t : ℝ) ^ ((1 : ℝ) / 100)
      ≤ c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by
    have h := hZ11 x hxZ11
    have ht100 : (t : ℝ) ^ ((1 : ℝ) / 100) ≤ (x : ℝ) ^ ((1 : ℝ) / 100) :=
      Real.rpow_le_rpow ht0 htle (by norm_num)
    have h1 : (N : ℝ) * (t : ℝ) ^ ((1 : ℝ) / 100)
        ≤ (x : ℝ) ^ Dmax * (x : ℝ) ^ ((1 : ℝ) / 100) :=
      mul_le_mul hNx ht100 (Real.rpow_nonneg ht0 _) (Real.rpow_nonneg hx0 _)
    have h2 : (x : ℝ) ^ Dmax * (x : ℝ) ^ ((1 : ℝ) / 100) = (x : ℝ) ^ (Dmax + 1 / 100) := by
      rw [← Real.rpow_add hxpos]
    have h3 : 2 * CAd2 * CAu * (N : ℝ) * (t : ℝ) ^ ((1 : ℝ) / 100)
        = (2 * CAd2 * CAu) * ((N : ℝ) * (t : ℝ) ^ ((1 : ℝ) / 100)) := by ring
    rw [h3]
    refine le_trans (mul_le_mul_of_nonneg_left (le_trans h1 h2.le) (by positivity)) ?_
    simpa only [Real.rpow_zero, mul_one] using h
  have he4 : 2 * CAu * Cg * (N : ℝ) * (Real.log (N : ℝ)) ^ Ag
      ≤ c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by
    have h := hZ12 x hxZ12
    have h1 : (N : ℝ) * (Real.log (N : ℝ)) ^ Ag
        ≤ (x : ℝ) ^ Dmax * (K4 * (Real.log x) ^ Agg) :=
      mul_le_mul hNx hlogAg (Real.rpow_nonneg hlogN0 _) (Real.rpow_nonneg hx0 _)
    have h2 : 2 * CAu * Cg * ((N : ℝ) * (Real.log (N : ℝ)) ^ Ag)
        ≤ 2 * CAu * Cg * ((x : ℝ) ^ Dmax * (K4 * (Real.log x) ^ Agg)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 2 * CAu * Cg * ((x : ℝ) ^ Dmax * (K4 * (Real.log x) ^ Agg))
        = (2 * CAu * Cg * K4) * (x : ℝ) ^ Dmax * (Real.log x) ^ Agg := by ring
    calc 2 * CAu * Cg * (N : ℝ) * (Real.log (N : ℝ)) ^ Ag
        = 2 * CAu * Cg * ((N : ℝ) * (Real.log (N : ℝ)) ^ Ag) := by ring
      _ ≤ 2 * CAu * Cg * ((x : ℝ) ^ Dmax * (K4 * (Real.log x) ^ Agg)) := h2
      _ = (2 * CAu * Cg * K4) * (x : ℝ) ^ Dmax * (Real.log x) ^ Agg := h3
      _ ≤ c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by
          simpa only [mul_assoc] using h
  -- ### final comparisons with `A(x)(log x)^{-lamm}`
  have hfin_c1 : c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)
      ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
    have h2 : c1 ≤ cAl := by rw [hc1def]; linarith [hcAl]
    have hxl0 : (0 : ℝ) ≤ (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) :=
      mul_nonneg (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg hlog0 _)
    calc c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)
        = c1 * ((x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)) := by ring
      _ ≤ cAl * ((x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)) :=
          mul_le_mul_of_nonneg_right h2 hxl0
      _ = cAl * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by ring
      _ ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) :=
          mul_le_mul_of_nonneg_right hAx (Real.rpow_nonneg hlog0 _)
  have hfin_4 : 4 * (c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm))
      ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
    have h2 : 4 * c1 ≤ cAl := by rw [hc1def]; linarith [hcAl]
    have hxl0 : (0 : ℝ) ≤ (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) :=
      mul_nonneg (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg hlog0 _)
    calc 4 * (c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm))
        = (4 * c1) * ((x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)) := by ring
      _ ≤ cAl * ((x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)) :=
          mul_le_mul_of_nonneg_right h2 hxl0
      _ = cAl * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by ring
      _ ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) :=
          mul_le_mul_of_nonneg_right hAx (Real.rpow_nonneg hlog0 _)
  have hfin_16 : 16 * (c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm))
      ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
    have h2 : 16 * c1 ≤ cAl := by rw [hc1def]; linarith [hcAl]
    have hxl0 : (0 : ℝ) ≤ (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) :=
      mul_nonneg (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg hlog0 _)
    calc 16 * (c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm))
        = (16 * c1) * ((x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)) := by ring
      _ ≤ cAl * ((x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)) :=
          mul_le_mul_of_nonneg_right h2 hxl0
      _ = cAl * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by ring
      _ ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) :=
          mul_le_mul_of_nonneg_right hAx (Real.rpow_nonneg hlog0 _)
  -- ### the crude case, packaged
  have hfin_crude : ∀ (_hcc : (∑ p ∈ Submission.ASP.CO4 N,
        |(Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ)
          - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ (N : ℝ) + 2 * CAd2 * CAu * (N : ℝ) * (t : ℝ) ^ ((1 : ℝ) / 100)
        + 2 * CAu * Cg * (N : ℝ) * (Real.log N) ^ Ag),
      (∑ d ∈ (Finset.range N).filter
          (fun d => (∀ p ∈ d.primeFactors, d.factorization p ≤ 2) ∧ 4 ∣ d),
          |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
        ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
    intro hcc
    have hdd := Submission.ASP.four_dvd_sum_le N t (by omega)
    have hS : (∑ d ∈ (Finset.range N).filter
          (fun d => (∀ p ∈ d.primeFactors, d.factorization p ≤ 2) ∧ 4 ∣ d),
          |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
        ≤ 1 + ((N : ℝ) + 2 * CAd2 * CAu * (N : ℝ) * (t : ℝ) ^ ((1 : ℝ) / 100)
          + 2 * CAu * Cg * (N : ℝ) * (Real.log N) ^ Ag) :=
      le_trans hdd (add_le_add le_rfl hcc)
    have hsum : 1 + ((N : ℝ) + 2 * CAd2 * CAu * (N : ℝ) * (t : ℝ) ^ ((1 : ℝ) / 100)
          + 2 * CAu * Cg * (N : ℝ) * (Real.log N) ^ Ag)
        ≤ 4 * (c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)) := by
      linarith [he1, he2, he3, he4, hX0]
    exact le_trans hS (le_trans hsum hfin_4)
  rcases lt_or_ge t 16 with ht16 | ht16
  · -- ### Case B : `t < 16`
    by_cases hN4 : 4 ≤ N
    · have htN : (t : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 * (N : ℝ) := by
        have h1 : (t : ℝ) < 16 := by exact_mod_cast ht16
        have h2 : (t : ℝ) ^ ((3 : ℝ) / 4) < (16 : ℝ) ^ ((3 : ℝ) / 4) :=
          Real.rpow_lt_rpow ht0 h1 (by norm_num)
        have h3 : (16 : ℝ) ^ ((3 : ℝ) / 4) = 8 := by
          rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 4,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
        rw [h3] at h2
        have h4N : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN4
        linarith
      exact hfin_crude (Submission.ASP.CO4_bound_crude N t hN3le hCAd2.le hCAu.le hCg.le
        hAd2 hAu hAg3 ht2 htN)
    · -- `N = 3`: the only admissible modulus is `0`
      have hNeq : N = 3 := le_antisymm (by omega) hN3le
      have hdd := Submission.ASP.four_dvd_sum_le N t (by omega)
      have hCO4 : Submission.ASP.CO4 N = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro p hp
        rw [Submission.ASP.CO4, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_Icc] at hp
        obtain ⟨⟨⟨ha1, haN⟩, ⟨hb1, hbN⟩⟩, -, -, -, -, hlt⟩ := hp
        have h2 : 1 ≤ p.2 ^ 2 := by nlinarith [hb1]
        have h3 : 1 ≤ p.1 * p.2 ^ 2 := by
          have := Nat.mul_le_mul ha1 h2
          simpa using this
        have h4 : 4 ≤ 4 * (p.1 * p.2 ^ 2) := Nat.mul_le_mul_left 4 h3
        omega
      rw [hCO4, Finset.sum_empty, add_zero] at hdd
      rw [four_dvd_filter_eq]
      exact le_trans hdd (le_trans he1 hfin_c1)
  · by_cases hcase : N ≤ ⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊
    · -- ### Case A : `16 ≤ t` and `N ≤ t^{3/4}`
      have hcf := Submission.ASP.CO4_bound_fine N t hN3le ht16 hcase hCAd hCMd hAd hMd hM4 hAs
        hAh3 hAg3 hInv hTau hCM4.le hCh.le hCg.le hCAs.le hκ0 hCt hCinv hAhM hAgM
      have hdd := Submission.ASP.four_dvd_sum_le N t (by omega)
      have hK16 : (((⌊((t : ℝ) / 16) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℝ) + 1)
          ≤ (x : ℝ) ^ ((1 : ℝ) / 4) + 1 := by
        have h1 : ((⌊((t : ℝ) / 16) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℝ) ≤ ((t : ℝ) / 16) ^ ((1 : ℝ) / 4) :=
          Nat.floor_le (by positivity)
        have h2 : ((t : ℝ) / 16) ^ ((1 : ℝ) / 4) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) := by
          rw [Real.div_rpow (by positivity) (by norm_num)]
          refine le_trans (div_le_self (Real.rpow_nonneg (by positivity) _) (by norm_num)) ?_
          exact Real.rpow_le_rpow (by positivity) htle (by norm_num)
        linarith
      have hcA1 : CAd * (N : ℝ) ^ ((1 : ℝ) / 4) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
          ≤ c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by
        have h := hZ1 x hxZ1
        have ht9 : (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) ≤ (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) :=
          Real.rpow_le_rpow ht0 htle (by norm_num)
        have h1 : (N : ℝ) ^ ((1 : ℝ) / 4) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
            ≤ (x : ℝ) ^ (Dmax * ((1 : ℝ) / 4)) * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100) :=
          mul_le_mul hN12 ht9 (Real.rpow_nonneg ht0 _) (Real.rpow_nonneg hx0 _)
        have h2 : (x : ℝ) ^ (Dmax * ((1 : ℝ) / 4)) * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
            = (x : ℝ) ^ (Dmax * ((1 : ℝ) / 4) + ((9 : ℝ) / 16 + 1 / 100)) := by
          rw [← Real.rpow_add hxpos]
        calc CAd * (N : ℝ) ^ ((1 : ℝ) / 4) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)
            = CAd * ((N : ℝ) ^ ((1 : ℝ) / 4) * (t : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)) := by ring
          _ ≤ CAd * ((x : ℝ) ^ (Dmax * ((1 : ℝ) / 4))
                * (x : ℝ) ^ ((9 : ℝ) / 16 + 1 / 100)) :=
              mul_le_mul_of_nonneg_left h1 hCAd.le
          _ = CAd * (x : ℝ) ^ (Dmax * ((1 : ℝ) / 4) + ((9 : ℝ) / 16 + 1 / 100)) := by rw [h2]
          _ ≤ c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by
              simpa only [Real.rpow_zero, mul_one] using h
      have hcA2 : CMd * (t : ℝ) ^ ((1 : ℝ) / 4) * (Real.log (2 * (N : ℝ) + 2)) ^ 6
          ≤ c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by
        have h := hZ2 x hxZ2
        have ht4 : (t : ℝ) ^ ((1 : ℝ) / 4) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow ht0 htle (by norm_num)
        have hl6 : (Real.log (2 * (N : ℝ) + 2)) ^ 6 ≤ (2 * Real.log x) ^ 6 :=
          pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlog2N2 6
        have h1 : CMd * (t : ℝ) ^ ((1 : ℝ) / 4) * (Real.log (2 * (N : ℝ) + 2)) ^ 6
            ≤ CMd * (x : ℝ) ^ ((1 : ℝ) / 4) * (2 * Real.log x) ^ 6 :=
          mul_le_mul (mul_le_mul_of_nonneg_left ht4 hCMd.le) hl6 (by positivity) (by positivity)
        refine le_trans h1 ?_
        have h2 : CMd * (x : ℝ) ^ ((1 : ℝ) / 4) * (2 * Real.log x) ^ 6
            = CMd * 64 * (x : ℝ) ^ ((1 : ℝ) / 4) * (Real.log x) ^ 6 := by ring
        rw [h2]
        have hc := h
        rw [show (Real.log x) ^ ((6 : ℝ)) = (Real.log x) ^ 6 from Real.rpow_natCast _ 6] at hc
        simpa only [mul_assoc] using hc
      have hcA3 : 16 * Real.sqrt (N : ℝ)
          ≤ c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by
        have h := hZ3 x hxZ3
        refine le_trans (mul_le_mul_of_nonneg_left hsqrtN (by norm_num : (0 : ℝ) ≤ 16)) ?_
        simpa only [Real.rpow_zero, mul_one] using h
      have hcA4 : 8 * Cinv
          ≤ c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by
        have h := hZ4 x hxZ4
        simpa only [Real.rpow_zero, mul_one, one_mul] using h
      have hcA5 : 4 * ((((⌊((t : ℝ) / 16) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℝ) + 1)
            * (Ct * (Real.log ((N : ℝ) + 2)) ^ 4))
          ≤ c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by
        have h5 : 256 * Ct * ((x : ℝ) ^ ((1 : ℝ) / 4) * (Real.log x) ^ 4)
            ≤ (c1 / 2) * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by
          have hc := hZ5 x hxZ5
          rw [show (Real.log x) ^ ((4 : ℝ)) = (Real.log x) ^ 4 from Real.rpow_natCast _ 4] at hc
          simpa only [mul_assoc] using hc
        have h6 : 256 * Ct * (Real.log x) ^ 4
            ≤ (c1 / 2) * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by
          have hc := hZ6 x hxZ6
          rw [show (Real.log x) ^ ((4 : ℝ)) = (Real.log x) ^ 4 from Real.rpow_natCast _ 4] at hc
          simpa only [Real.rpow_zero, mul_one, mul_assoc] using hc
        have hl4 : (Real.log ((N : ℝ) + 2)) ^ 4 ≤ 64 * (Real.log x) ^ 4 := by
          have h1 : (Real.log ((N : ℝ) + 2)) ^ 4 ≤ (2 * Real.log x) ^ 4 :=
            pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlogNp2 4
          have h2 : (2 * Real.log x) ^ 4 = 16 * (Real.log x) ^ 4 := by ring
          have h3 : 16 * (Real.log x) ^ 4 ≤ 64 * (Real.log x) ^ 4 :=
            mul_le_mul_of_nonneg_right (by norm_num : (16 : ℝ) ≤ 64) (pow_nonneg hlog0 4)
          linarith [h1, h2.le, h3]
        have h88 : 4 * ((((⌊((t : ℝ) / 16) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℝ) + 1)
              * (Ct * (Real.log ((N : ℝ) + 2)) ^ 4))
            ≤ 256 * Ct * ((x : ℝ) ^ ((1 : ℝ) / 4) * (Real.log x) ^ 4)
              + 256 * Ct * (Real.log x) ^ 4 := by
          have ha : 4 * ((((⌊((t : ℝ) / 16) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℝ) + 1)
                * (Ct * (Real.log ((N : ℝ) + 2)) ^ 4))
              ≤ 4 * (((x : ℝ) ^ ((1 : ℝ) / 4) + 1) * (Ct * (64 * (Real.log x) ^ 4))) := by
            refine mul_le_mul le_rfl ?_ (by positivity) (by positivity)
            exact mul_le_mul hK16 (mul_le_mul_of_nonneg_left hl4 hCt.le) (by positivity)
              (by positivity)
          refine le_trans ha (le_of_eq ?_)
          ring
        have hsum2 : (c1 / 2) * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)
              + (c1 / 2) * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)
            ≤ c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := le_of_eq (by ring)
        exact le_trans h88 (le_trans (add_le_add h5 h6) hsum2)
      have hcA6 : KK * (Real.log (N : ℝ)) ^ M * (Real.sqrt (t : ℝ) + 1)
          ≤ 2 * (c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)) := by
        have h8 : KK * K4 * (Real.log x) ^ M
            ≤ c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by
          simpa only [Real.rpow_zero, mul_one] using hZ8 x hxZ8
        have h7 : KK * K4 * (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ M
            ≤ c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by
          simpa only [mul_assoc] using hZ7 x hxZ7
        have hst : Real.sqrt (t : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow ht0 htle (by norm_num)
        have h10 : (Real.log (N : ℝ)) ^ M * (Real.sqrt (t : ℝ) + 1)
            ≤ (K4 * (Real.log x) ^ M) * ((x : ℝ) ^ ((1 : ℝ) / 2) + 1) :=
          mul_le_mul hlogNM (by linarith) (by positivity)
            (mul_nonneg hK40.le (Real.rpow_nonneg hlog0 _))
        have h10' : KK * ((Real.log (N : ℝ)) ^ M * (Real.sqrt (t : ℝ) + 1))
            ≤ KK * ((K4 * (Real.log x) ^ M) * ((x : ℝ) ^ ((1 : ℝ) / 2) + 1)) :=
          mul_le_mul_of_nonneg_left h10 hKK0
        have hgoal1 : KK * (Real.log (N : ℝ)) ^ M * (Real.sqrt (t : ℝ) + 1)
            ≤ KK * ((K4 * (Real.log x) ^ M) * ((x : ℝ) ^ ((1 : ℝ) / 2) + 1)) := by
          simpa only [mul_assoc] using h10'
        refine le_trans hgoal1 ?_
        rw [show KK * ((K4 * (Real.log x) ^ M) * ((x : ℝ) ^ ((1 : ℝ) / 2) + 1))
            = KK * K4 * (x : ℝ) ^ ((1 : ℝ) / 2) * (Real.log x) ^ M
              + KK * K4 * (Real.log x) ^ M from by ring]
        have hsum2 : c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)
              + c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)
            ≤ 2 * (c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)) := le_of_eq (by ring)
        exact le_trans (add_le_add h7 h8) hsum2
      have hmidA : 2 * (4 * (2 * Real.sqrt (N : ℝ) + Cinv)
            + 2 * ((((⌊((t : ℝ) / 16) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℝ) + 1)
              * (Ct * (Real.log ((N : ℝ) + 2)) ^ 4)))
          ≤ 3 * (c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)) := by
        set Z : ℝ := ((((⌊((t : ℝ) / 16) ^ ((1 : ℝ) / 4)⌋₊ : ℕ) : ℝ) + 1)
          * (Ct * (Real.log ((N : ℝ) + 2)) ^ 4)) with hZdef
        have hZ5' : 4 * Z ≤ c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm) := by
          rw [hZdef]; exact hcA5
        rw [show 2 * (4 * (2 * Real.sqrt (N : ℝ) + Cinv) + 2 * Z)
            = 16 * Real.sqrt (N : ℝ) + 8 * Cinv + 4 * Z from by ring]
        linarith [hcA3, hcA4, hZ5', hX0]
      have hT : (∑ p ∈ Submission.ASP.CO4 N, |(Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ)
            - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)|)
          ≤ c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)
            + c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)
            + 3 * (c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm))
            + 2 * (c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)) := by
        linarith [hcf, hcA1, hcA2, hmidA, hcA6, hKKdef]
      have hS : (∑ d ∈ (Finset.range N).filter
            (fun d => (∀ p ∈ d.primeFactors, d.factorization p ≤ 2) ∧ 4 ∣ d),
            |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
          ≤ 1 + (c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)
            + c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)
            + 3 * (c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm))
            + 2 * (c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm))) :=
        le_trans hdd (add_le_add le_rfl hT)
      have hsumA : 1 + (c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)
            + c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)
            + 3 * (c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm))
            + 2 * (c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)))
          ≤ 16 * (c1 * (x : ℝ) ^ ((3 : ℝ) / 4) * (Real.log x) ^ (-lamm)) := by
        linarith [he1, hX0]
      have hgoal : (∑ d ∈ (Finset.range N).filter
            (fun d => (∀ p ∈ d.primeFactors, d.factorization p ≤ 2) ∧ 4 ∣ d),
            |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
          ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) :=
        le_trans hS (le_trans hsumA hfin_16)
      rw [four_dvd_filter_eq]
      exact hgoal
    · -- ### Case C : `t^{3/4} < N`, crude
      have htN : (t : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 * (N : ℝ) := by
        have h1 : ((⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ : ℕ) : ℝ) ≤ (t : ℝ) ^ ((3 : ℝ) / 4) :=
          Nat.floor_le (by positivity)
        have h2 : (t : ℝ) ^ ((3 : ℝ) / 4) < ((⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ : ℕ) : ℝ) + 1 :=
          Nat.lt_floor_add_one _
        have h3 : ((⌊(t : ℝ) ^ ((3 : ℝ) / 4)⌋₊ : ℕ) : ℝ) < (N : ℝ) := by
          exact_mod_cast (Nat.lt_of_not_le hcase)
        have h4 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
        linarith
      exact hfin_crude (Submission.ASP.CO4_bound_crude N t hN3le hCAd2.le hCAu.le hCg.le
        hAd2 hAu hAg3 ht2 htN)

end

end Work.FIChain
