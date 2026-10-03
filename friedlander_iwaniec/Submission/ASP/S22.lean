import Mathlib
import Submission.ASP.S21
import Submission.ASP_R3

set_option maxHeartbeats 4000000

namespace Submission.ASP
open Finset
noncomputable section

/-- The `4 ∣ d` part of hypothesis `(R₃)`. -/
theorem R3_four_part_generic (lamm : ℝ) : ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
    (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter
        (fun d => (∀ p ∈ d.primeFactors, d.factorization p ≤ 2) ∧ 4 ∣ d),
      |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
    ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
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
  obtain ⟨XRs, hRself⟩ := Submission.X2Y4R3.R3cut_le_self
  have hAh3 : ∀ y : ℕ, 3 ≤ y → Submission.X2Y4R.cubeSum y
      (fun a b => (Submission.hdens a b : ℝ)) ≤ Ch * (Real.log y) ^ Ah :=
    fun y hy => hHh y (by omega)
  have hAg3 : ∀ y : ℕ, 3 ≤ y → Submission.X2Y4R.cubeSum y
      (fun a b => |(Submission.gdens (a * b ^ 2) : ℝ)|) ≤ Cg * (Real.log y) ^ Ag :=
    fun y hy => hGg y (by omega)
  set Ahh : ℝ := max Ah 0 with hAhhdef
  set Agg : ℝ := max Ag 0 with hAggdef
  have hAhh0 : 0 ≤ Ahh := by rw [hAhhdef]; exact le_max_right _ _
  have hAgg0 : 0 ≤ Agg := by rw [hAggdef]; exact le_max_right _ _
  have hAhh : Ah ≤ Ahh := by rw [hAhhdef]; exact le_max_left _ _
  have hAgg : Ag ≤ Agg := by rw [hAggdef]; exact le_max_left _ _
  set M : ℝ := Ahh + Agg + 10 with hMdef
  have hAhM : Ah ≤ M := by rw [hMdef]; linarith [hAhh]
  have hAgM : Ag ≤ M := by rw [hMdef]; linarith [hAgg]
  have hM1 : (1:ℝ) ≤ M := by rw [hMdef]; linarith [hAhh0, hAgg0]
  set K4 : ℝ := (2:ℝ)^(26 * ⌈M⌉₊) + 1 with hK4def
  have hK41 : (1:ℝ) ≤ K4 := by
    rw [hK4def]
    have h2 : (1:ℝ) ≤ (2:ℝ)^(26 * ⌈M⌉₊) := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    linarith
  have hK40 : (0:ℝ) < K4 := lt_of_lt_of_le zero_lt_one hK41
  set c1 : ℝ := cAl / 16 with hc1def
  have hc1 : 0 < c1 := by rw [hc1def]; positivity
  have hc10 : 0 ≤ c1 := le_of_lt hc1
  have hκ0 : (0:ℝ) ≤ ∫ u in (0)..1, Real.sqrt (1 - u^4) :=
    intervalIntegral.integral_nonneg (by norm_num) (fun t _ => Real.sqrt_nonneg _)
  set KK : ℝ := 2 * CM4 * Ch + 32 * (∫ u in (0)..1, Real.sqrt (1 - u^4)) * Cg + CAs * Cg
    with hKKdef
  have hKK0 : 0 ≤ KK := by rw [hKKdef]; positivity
  -- polylog comparisons
  obtain ⟨Z1, hZ1x, hZ1⟩ := Submission.X2Y4R3.poly_tail_gen CAd (7/40 + ((9:ℝ)/16 + 1/100))
    ((2:ℝ)^23) c1 lamm hCAd (by norm_num) hc1
  obtain ⟨Z2, hZ2x, hZ2⟩ := Submission.X2Y4R3.poly_tail_gen (CMd * 64) (1/4) 6 c1
    lamm (by positivity) (by norm_num) hc1
  obtain ⟨Z3, hZ3x, hZ3⟩ := Submission.X2Y4R3.poly_tail_gen 16 (7/20) ((2:ℝ)^24) c1
    lamm (by norm_num) (by norm_num) hc1
  obtain ⟨Z4, hZ4x, hZ4⟩ := Submission.X2Y4R3.poly_tail_gen (8 * Cinv) 0 0 c1 lamm
    (by positivity) (by norm_num) hc1
  obtain ⟨Z5, hZ5x, hZ5⟩ := Submission.X2Y4R3.poly_tail_gen (256 * Ct) (1/4) 4 (c1/2)
    lamm (by positivity) (by norm_num) (by positivity)
  obtain ⟨Z6, hZ6x, hZ6⟩ := Submission.X2Y4R3.poly_tail_gen (256 * Ct) 0 4 (c1/2)
    lamm (by positivity) (by norm_num) (by positivity)
  obtain ⟨Z7, hZ7x, hZ7⟩ := Submission.X2Y4R3.poly_tail_gen (KK * K4) (1/2) M c1 lamm
    (by positivity) (by norm_num) hc1
  obtain ⟨Z8, hZ8x, hZ8⟩ := Submission.X2Y4R3.poly_tail_gen (KK * K4) 0 M c1 lamm
    (by positivity) (by norm_num) hc1
  obtain ⟨Z9, hZ9x, hZ9⟩ := Submission.X2Y4R3.poly_tail_gen 1 0 0 c1 lamm
    (by norm_num) (by norm_num) hc1
  obtain ⟨Z10, hZ10x, hZ10⟩ := Submission.X2Y4R3.poly_tail_gen 1 (7/10) ((2:ℝ)^25) c1
    lamm (by norm_num) (by norm_num) hc1
  obtain ⟨Z11, hZ11x, hZ11⟩ := Submission.X2Y4R3.poly_tail_gen (2 * CAd2 * CAu) (71/100)
    ((2:ℝ)^25) c1 lamm (by positivity) (by norm_num) hc1
  obtain ⟨Z12, hZ12x, hZ12⟩ := Submission.X2Y4R3.poly_tail_gen (2 * CAu * Cg * K4) (7/10)
    ((2:ℝ)^25 + Agg) c1 lamm (by positivity) (by norm_num) hc1
  refine ⟨Z1 + Z2 + Z3 + Z4 + Z5 + Z6 + Z7 + Z8 + Z9 + Z10 + Z11 + Z12 + XRs + XAl + 100,
    fun x hx t ht2 htx => ?_⟩
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
  have hxXRs : XRs ≤ x := by omega
  have hxXAl : XAl ≤ x := by omega
  have hx6 : 6 ≤ x := by omega
  have hxR : (5 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 5 ≤ x)
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hxpos
  have hlog1 : 1 ≤ Real.log x := by
    have hexp : Real.exp 1 ≤ (x : ℝ) := by linarith [Real.exp_one_lt_d9]
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hlog0 : 0 ≤ Real.log x := le_trans zero_le_one hlog1
  have hlogpos : (0 : ℝ) < Real.log x := lt_of_lt_of_le zero_lt_one hlog1
  have htle : (t : ℝ) ≤ (x : ℝ) := by exact_mod_cast htx
  have ht1 : 1 ≤ t := by omega
  have hAx : cAl * (x : ℝ) ^ ((3 : ℝ) / 4) ≤ (Submission.Aseq x : ℝ) := hAl x hxXAl
  have hlogz : (0 : ℝ) ≤ (Real.log x) ^ (-((2 : ℝ) ^ 25)) := Real.rpow_nonneg hlog0 _
  set N : ℕ := Submission.X2Y4R3.R3cut x with hNdef
  have hN2 : 2 ≤ N := by rw [hNdef]; exact Submission.X2Y4R3.two_le_R3cut (by omega)
  have hN4 : 4 ≤ N := by
    rw [hNdef]
    refine Nat.le_floor ?_
    have h6 : (4:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 4 ≤ x)
    have hx1 : (1:ℝ) ≤ (x:ℝ) := by linarith
    have h8r : (4:ℝ) ≤ (8:ℝ) ^ ((7:ℝ)/10) := by
      have e : (8:ℝ) ^ ((7:ℝ)/10) = (2:ℝ) ^ (3 * ((7:ℝ)/10)) := by
        rw [show (8:ℝ) = (2:ℝ)^(3:ℕ) by norm_num, ← Real.rpow_natCast (2:ℝ) 3,
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
      rw [e, show (4:ℝ) = (2:ℝ)^(2:ℕ) by norm_num, ← Real.rpow_natCast (2:ℝ) 2]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h1 : (4:ℝ) ≤ (x:ℝ) ^ ((7:ℝ)/10) := by
      refine le_trans h8r (Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 8)
        (by exact_mod_cast (by omega : 8 ≤ x)) (by norm_num : (0:ℝ) ≤ (7:ℝ)/10))
    have h3 : (1:ℝ) ≤ (Real.log x) ^ ((2:ℝ)^25) := Real.one_le_rpow hlog1 (by norm_num)
    calc (4:ℝ) ≤ (x:ℝ) ^ ((7:ℝ)/10) := h1
      _ ≤ (x:ℝ) ^ ((7:ℝ)/10) * (Real.log x) ^ ((2:ℝ)^25) :=
          le_mul_of_one_le_right (Real.rpow_nonneg hx0 _) h3
  have hNle : (N:ℝ) ≤ (x:ℝ) := by
    rw [hNdef]; exact_mod_cast (hRself x hxXRs)
  have hNup : (N:ℝ) ≤ (x:ℝ) ^ ((7:ℝ)/10) * (Real.log x) ^ ((2:ℝ)^25) := by
    rw [hNdef, Submission.X2Y4R3.R3cut]
    exact Nat.floor_le (by positivity)
  have hlogN_le : Real.log (N:ℝ) ≤ (2:ℝ)^26 * Real.log x := by
    have h1 : Real.log ((N:ℝ)) ≤ Real.log ((x:ℝ) ^ ((7:ℝ)/10) * (Real.log x) ^ ((2:ℝ)^25)) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) hNup
    rw [Real.log_mul (Real.rpow_pos_of_pos hxpos _).ne'
        (Real.rpow_pos_of_pos hlogpos _).ne', Real.log_rpow hxpos, Real.log_rpow hlogpos] at h1
    have h2 : Real.log x ^ ((2:ℝ)^25 - 1) ≤ Real.log x ^ ((2:ℝ)^26 - 1) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
    have hll : Real.log (Real.log x) ≤ Real.log x := Real.log_le_self hlog0
    nlinarith [h1, h2, hll, hlog0, Real.rpow_pos_of_pos hlogpos ((2:ℝ)^25 - 1)]
  have hlogN0 : (0:ℝ) ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hlogN1 : (1:ℝ) ≤ Real.log (N:ℝ) := by
    have h3 : (1:ℝ) ≤ Real.log 3 := by
      have h := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9] : Real.exp 1 ≤ 3)
      rwa [Real.log_exp] at h
    have h4 : (3:ℝ) ≤ (N:ℝ) := by exact_mod_cast (by omega : 3 ≤ N)
    have h5 := Real.log_le_log (by norm_num) h4
    linarith
  -- ## `(log N)^Agg` and `(log N)^M` are absorbed by `K4 (log x)^·`
  have pow26_le : ∀ A : ℝ, A ≤ (⌈M⌉₊ : ℝ) → ((2:ℝ)^(26:ℕ)) ^ A ≤ (2:ℝ)^(26 * ⌈M⌉₊) := by
    intro A hA
    calc ((2:ℝ)^(26:ℕ)) ^ A ≤ ((2:ℝ)^(26:ℕ)) ^ (⌈M⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hA
      _ = (2:ℝ) ^ (26 * ⌈M⌉₊) := by rw [Real.rpow_natCast, ← pow_mul]
  have hAggle : Agg ≤ (⌈M⌉₊ : ℝ) := by
    rw [hAggdef]
    exact max_le (le_trans hAgM (Nat.le_ceil M)) (by positivity)
  have hlogNAgg : (Real.log (N:ℝ)) ^ Agg ≤ K4 * (Real.log x) ^ Agg := by
    have h1 : (Real.log (N:ℝ)) ^ Agg ≤ ((2:ℝ)^(26:ℕ) * Real.log x) ^ Agg :=
      Real.rpow_le_rpow hlogN0 hlogN_le hAgg0
    rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ (2:ℝ)^(26:ℕ)) hlog0] at h1
    calc (Real.log (N:ℝ)) ^ Agg ≤ ((2:ℝ)^(26:ℕ)) ^ Agg * (Real.log x) ^ Agg := h1
      _ ≤ (2:ℝ) ^ (26 * ⌈M⌉₊) * (Real.log x) ^ Agg :=
          mul_le_mul_of_nonneg_right (pow26_le Agg hAggle) (Real.rpow_nonneg hlog0 _)
      _ ≤ K4 * (Real.log x) ^ Agg := by
          rw [hK4def]
          exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hlog0 _)
  have hlogNM : (Real.log (N:ℝ)) ^ M ≤ K4 * (Real.log x) ^ M := by
    have h1 : (Real.log (N:ℝ)) ^ M ≤ ((2:ℝ)^(26:ℕ) * Real.log x) ^ M :=
      Real.rpow_le_rpow hlogN0 hlogN_le (le_trans zero_le_one hM1)
    rw [Real.mul_rpow (by positivity : (0:ℝ) ≤ (2:ℝ)^(26:ℕ)) hlog0] at h1
    calc (Real.log (N:ℝ)) ^ M ≤ ((2:ℝ)^(26:ℕ)) ^ M * (Real.log x) ^ M := h1
      _ ≤ (2:ℝ) ^ (26 * ⌈M⌉₊) * (Real.log x) ^ M :=
          mul_le_mul_of_nonneg_right (pow26_le M (Nat.le_ceil M)) (Real.rpow_nonneg hlog0 _)
      _ ≤ K4 * (Real.log x) ^ M := by
          rw [hK4def]
          exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hlog0 _)
  have hlogNp2 : Real.log ((N:ℝ) + 2) ≤ 2 * Real.log x := by
    have h1 : (N:ℝ) + 2 ≤ 4 * (x:ℝ) := by linarith
    have h2 : Real.log ((N:ℝ)+2) ≤ Real.log (4 * (x:ℝ)) :=
      Real.log_le_log (by linarith) h1
    have h3 : Real.log (4 * (x:ℝ)) = Real.log 4 + Real.log x :=
      Real.log_mul (by norm_num) (ne_of_gt hxpos)
    have h4 : Real.log 4 ≤ Real.log x :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 4 ≤ x))
    linarith [h2, h3, h4]
  have hlog2N2 : Real.log (2 * (N:ℝ) + 2) ≤ 2 * Real.log x := by
    have h1 : 2 * (N:ℝ) + 2 ≤ 6 * (x:ℝ) := by linarith
    have h2 : Real.log (2 * (N:ℝ)+2) ≤ Real.log (6 * (x:ℝ)) :=
      Real.log_le_log (by linarith) h1
    have h3 : Real.log (6 * (x:ℝ)) = Real.log 6 + Real.log x :=
      Real.log_mul (by norm_num) (ne_of_gt hxpos)
    have h4 : Real.log 6 ≤ Real.log x := Real.log_le_log (by norm_num) (by exact_mod_cast hx6)
    linarith [h2, h3, h4]
  have hN12 : (N:ℝ) ^ ((1:ℝ)/4) ≤ (x:ℝ) ^ ((7:ℝ)/40) * (Real.log x) ^ ((2:ℝ)^23) := by
    have h2 := Real.rpow_le_rpow (by positivity) hNup (by norm_num : (0:ℝ) ≤ (1:ℝ)/4)
    rw [Real.mul_rpow (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg hlog0 _)] at h2
    refine le_trans h2 ?_
    have e1 : ((x:ℝ) ^ ((7:ℝ)/10)) ^ ((1:ℝ)/4) ≤ (x:ℝ) ^ ((7:ℝ)/40) := by
      rw [← Real.rpow_mul hx0]; norm_num
    have e2 : ((Real.log x) ^ ((2:ℝ)^25)) ^ ((1:ℝ)/4) ≤ (Real.log x) ^ ((2:ℝ)^23) := by
      rw [← Real.rpow_mul hlog0]; norm_num
    exact mul_le_mul e1 e2 (Real.rpow_nonneg (Real.rpow_nonneg hlog0 _) _)
      (Real.rpow_nonneg hx0 _)
  have hsqrtN : Real.sqrt (N:ℝ) ≤ (x:ℝ) ^ ((7:ℝ)/20) * (Real.log x) ^ ((2:ℝ)^24) := by
    rw [Real.sqrt_eq_rpow]
    have h2 := Real.rpow_le_rpow (by positivity) hNup (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)
    rw [Real.mul_rpow (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg hlog0 _)] at h2
    refine le_trans h2 ?_
    have e1 : ((x:ℝ) ^ ((7:ℝ)/10)) ^ ((1:ℝ)/2) ≤ (x:ℝ) ^ ((7:ℝ)/20) := by
      rw [← Real.rpow_mul hx0]; norm_num
    have e2 : ((Real.log x) ^ ((2:ℝ)^25)) ^ ((1:ℝ)/2) ≤ (Real.log x) ^ ((2:ℝ)^24) := by
      rw [← Real.rpow_mul hlog0]; norm_num
    exact mul_le_mul e1 e2 (Real.rpow_nonneg (Real.rpow_nonneg hlog0 _) _)
      (Real.rpow_nonneg hx0 _)
  -- ## The polylog pieces
  have hX0 : (0:ℝ) ≤ c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm)) :=
    mul_nonneg (mul_nonneg hc10 (Real.rpow_nonneg hx0 _)) (Real.rpow_nonneg hlog0 _)
  have he1 : (1:ℝ) ≤ c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm)) := by
    have h := hZ9 x hxZ9
    simpa only [Real.rpow_zero, mul_one, one_mul] using h
  have he2 : (N:ℝ) ≤ c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm)) := by
    have h := hZ10 x hxZ10
    refine le_trans hNup ?_
    simpa only [one_mul] using h
  have he3 : 2 * CAd2 * CAu * (N:ℝ) * (t:ℝ)^((1:ℝ)/100)
      ≤ c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm)) := by
    have h := hZ11 x hxZ11
    have ht100 : (t:ℝ)^((1:ℝ)/100) ≤ (x:ℝ)^((1:ℝ)/100) :=
      Real.rpow_le_rpow (by positivity) htle (by norm_num)
    have h1 : 2 * CAd2 * CAu * (N:ℝ) * (t:ℝ)^((1:ℝ)/100)
        ≤ 2 * CAd2 * CAu * ((x:ℝ)^((7:ℝ)/10) * (Real.log x)^((2:ℝ)^25))
          * (x:ℝ)^((1:ℝ)/100) := by
      have h2 := mul_le_mul_of_nonneg_left hNup (by positivity : (0:ℝ) ≤ 2 * CAd2 * CAu)
      exact mul_le_mul h2 ht100 (Real.rpow_nonneg (by positivity) _) (by positivity)
    refine le_trans h1 ?_
    have hkey : 2 * CAd2 * CAu * ((x:ℝ)^((7:ℝ)/10) * (Real.log x)^((2:ℝ)^25))
          * (x:ℝ)^((1:ℝ)/100)
        = (2 * CAd2 * CAu) * ((x:ℝ)^((7:ℝ)/10) * (x:ℝ)^((1:ℝ)/100))
          * (Real.log x)^((2:ℝ)^25) := by ring
    have hpow : (x:ℝ)^((7:ℝ)/10) * (x:ℝ)^((1:ℝ)/100) = (x:ℝ)^((71:ℝ)/100) := by
      rw [← Real.rpow_add hxpos]; norm_num
    rw [hkey, hpow]
    simpa only [mul_assoc] using h
  have he4 : 2 * CAu * Cg * (N:ℝ) * (Real.log N) ^ Ag
      ≤ c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm)) := by
    have h := hZ12 x hxZ12
    have h1 : (Real.log (N:ℝ)) ^ Ag ≤ K4 * (Real.log x) ^ Agg :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hlogN1 hAgg) hlogNAgg
    have h2 : 2 * CAu * Cg * (N:ℝ) * (Real.log N) ^ Ag
        ≤ 2 * CAu * Cg * ((x:ℝ)^((7:ℝ)/10) * (Real.log x)^((2:ℝ)^25))
          * (K4 * (Real.log x)^Agg) := by
      have h3 := mul_le_mul hNup h1 (Real.rpow_nonneg hlogN0 _) (by positivity)
      have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ 2 * CAu * Cg)
      simpa only [mul_assoc] using h4
    refine le_trans h2 ?_
    have hkey : 2 * CAu * Cg * ((x:ℝ)^((7:ℝ)/10) * (Real.log x)^((2:ℝ)^25))
          * (K4 * (Real.log x)^Agg)
        = (2 * CAu * Cg * K4) * (x:ℝ)^((7:ℝ)/10)
          * ((Real.log x)^((2:ℝ)^25) * (Real.log x)^Agg) := by ring
    rw [hkey, ← Real.rpow_add hlogpos]
    simpa only [mul_assoc] using h
  have hfin_4 : 4 * (c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm)))
      ≤ (Submission.Aseq x : ℝ) * (Real.log x)^((-lamm)) := by
    have h2 : 4 * c1 ≤ cAl := by rw [hc1def]; linarith [hcAl]
    have hxl0 : (0:ℝ) ≤ (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm)) :=
      mul_nonneg (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg hlog0 _)
    calc 4 * (c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm)))
        = (4 * c1) * ((x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm))) := by ring
      _ ≤ cAl * ((x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm))) :=
          mul_le_mul_of_nonneg_right h2 hxl0
      _ = cAl * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm)) := by ring
      _ ≤ (Submission.Aseq x : ℝ) * (Real.log x)^((-lamm)) :=
          mul_le_mul_of_nonneg_right hAx (Real.rpow_nonneg hlog0 _)
  have hfin_16 : 16 * (c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm)))
      ≤ (Submission.Aseq x : ℝ) * (Real.log x)^((-lamm)) := by
    have h2 : 16 * c1 ≤ cAl := by rw [hc1def]; linarith [hcAl]
    have hxl0 : (0:ℝ) ≤ (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm)) :=
      mul_nonneg (Real.rpow_nonneg hx0 _) (Real.rpow_nonneg hlog0 _)
    calc 16 * (c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm)))
        = (16 * c1) * ((x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm))) := by ring
      _ ≤ cAl * ((x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm))) :=
          mul_le_mul_of_nonneg_right h2 hxl0
      _ = cAl * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm)) := by ring
      _ ≤ (Submission.Aseq x : ℝ) * (Real.log x)^((-lamm)) :=
          mul_le_mul_of_nonneg_right hAx (Real.rpow_nonneg hlog0 _)
  have hfin_crude : ∀ (hcc : (∑ p ∈ CO4 N, |(Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ)
        - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ (N:ℝ) + 2 * CAd2 * CAu * (N:ℝ) * (t:ℝ)^((1:ℝ)/100)
        + 2 * CAu * Cg * (N:ℝ) * (Real.log N) ^ Ag),
      (∑ d ∈ (Finset.range N).filter
        (fun d => (∀ p ∈ d.primeFactors, d.factorization p ≤ 2) ∧ 4 ∣ d),
        |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ (Submission.Aseq x : ℝ) * (Real.log x)^((-lamm)) := by
    intro hcc
    have hdd := four_dvd_sum_le N t (by omega)
    have hS : (∑ d ∈ (Finset.range N).filter
          (fun d => (∀ p ∈ d.primeFactors, d.factorization p ≤ 2) ∧ 4 ∣ d),
          |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
        ≤ 1 + ((N:ℝ) + 2 * CAd2 * CAu * (N:ℝ) * (t:ℝ)^((1:ℝ)/100)
          + 2 * CAu * Cg * (N:ℝ) * (Real.log N) ^ Ag) :=
      le_trans hdd (add_le_add le_rfl hcc)
    have hsum : 1 + ((N:ℝ) + 2 * CAd2 * CAu * (N:ℝ) * (t:ℝ)^((1:ℝ)/100)
          + 2 * CAu * Cg * (N:ℝ) * (Real.log N) ^ Ag)
        ≤ 4 * (c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm))) := by
      linarith [he1, he2, he3, he4, hX0]
    exact le_trans hS (le_trans hsum hfin_4)
  rcases Nat.lt_or_ge t 16 with ht16 | ht16
  · -- ## Case B: `t < 16`
    have htN : (t:ℝ)^((3:ℝ)/4) ≤ 2 * (N:ℝ) := by
      have h1 : (t:ℝ) < 16 := by exact_mod_cast ht16
      have h2 : (t:ℝ)^((3:ℝ)/4) < (16:ℝ)^((3:ℝ)/4) :=
        Real.rpow_lt_rpow (by positivity) h1 (by norm_num)
      have h3 : (16:ℝ)^((3:ℝ)/4) = 8 := by
        rw [show (16:ℝ) = 2^(4:ℕ) by norm_num, ← Real.rpow_natCast (2:ℝ) 4,
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
      rw [h3] at h2
      have h4N : (4:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN4
      linarith
    exact hfin_crude (CO4_bound_crude N t (by omega) hCAd2.le hCAu.le hCg.le hAd2 hAu hAg3 ht2 htN)
  · by_cases hcase : N ≤ ⌊(t:ℝ)^((3:ℝ)/4)⌋₊
    · -- ## Case A: `16 ≤ t` and `N ≤ t^{3/4}`
      have hcf := CO4_bound_fine N t (by omega) ht16 hcase hCAd hCMd hAd hMd hM4 hAs hAh3 hAg3
        hInv hTau hCM4.le hCh.le hCg.le hCAs.le hκ0 hCt hCinv hAhM hAgM
      have hdd := four_dvd_sum_le N t (by omega)
      have hK16 : (((⌊((t:ℝ)/16)^((1:ℝ)/4)⌋₊ : ℕ) : ℝ) + 1) ≤ (x:ℝ)^((1:ℝ)/4) + 1 := by
        have h1 : ((⌊((t:ℝ)/16)^((1:ℝ)/4)⌋₊ : ℕ) : ℝ) ≤ ((t:ℝ)/16)^((1:ℝ)/4) :=
          Nat.floor_le (by positivity)
        have h2 : ((t:ℝ)/16)^((1:ℝ)/4) ≤ (x:ℝ)^((1:ℝ)/4) := by
          rw [Real.div_rpow (by positivity) (by norm_num)]
          refine le_trans (div_le_self (Real.rpow_nonneg (by positivity) _) (by norm_num)) ?_
          exact Real.rpow_le_rpow (by positivity) htle (by norm_num)
        linarith
      have hcA1 : CAd * (N:ℝ)^((1:ℝ)/4) * (t:ℝ)^((9:ℝ)/16 + 1/100)
          ≤ c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm)) := by
        have h := hZ1 x hxZ1
        have h1 : (N:ℝ)^((1:ℝ)/4) * (t:ℝ)^((9:ℝ)/16 + 1/100)
            ≤ ((x:ℝ)^((7:ℝ)/40) * (Real.log x) ^ ((2:ℝ)^23))
              * (x:ℝ)^((9:ℝ)/16 + 1/100) := by
          have ht9 : (t:ℝ)^((9:ℝ)/16 + 1/100) ≤ (x:ℝ)^((9:ℝ)/16 + 1/100) :=
            Real.rpow_le_rpow (by positivity) htle (by norm_num)
          exact mul_le_mul hN12 ht9 (Real.rpow_nonneg (by positivity) _) (by positivity)
        have h2 : CAd * ((N:ℝ)^((1:ℝ)/4) * (t:ℝ)^((9:ℝ)/16 + 1/100))
            ≤ CAd * (((x:ℝ)^((7:ℝ)/40) * (Real.log x) ^ ((2:ℝ)^23))
              * (x:ℝ)^((9:ℝ)/16 + 1/100)) :=
          mul_le_mul_of_nonneg_left h1 hCAd.le
        have h3 : CAd * (N:ℝ)^((1:ℝ)/4) * (t:ℝ)^((9:ℝ)/16 + 1/100)
            ≤ CAd * (((x:ℝ)^((7:ℝ)/40) * (Real.log x) ^ ((2:ℝ)^23))
              * (x:ℝ)^((9:ℝ)/16 + 1/100)) := by
          simpa only [mul_assoc] using h2
        refine le_trans h3 ?_
        have h4 : CAd * (((x:ℝ)^((7:ℝ)/40) * (Real.log x) ^ ((2:ℝ)^23))
              * (x:ℝ)^((9:ℝ)/16 + 1/100))
            = CAd * (x:ℝ)^((7:ℝ)/40 + ((9:ℝ)/16 + 1/100))
              * (Real.log x) ^ ((2:ℝ)^23) := by
          rw [show ((x:ℝ)^((7:ℝ)/40) * (Real.log x) ^ ((2:ℝ)^23))
                * (x:ℝ)^((9:ℝ)/16 + 1/100)
              = (x:ℝ)^((7:ℝ)/40) * (x:ℝ)^((9:ℝ)/16 + 1/100)
                * (Real.log x) ^ ((2:ℝ)^23) from by ring,
            ← Real.rpow_add hxpos]
          ring
        rw [h4]
        exact h
      have hcA2 : CMd * (t:ℝ)^((1:ℝ)/4) * (Real.log (2 * (N:ℝ) + 2)) ^ 6
          ≤ c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm)) := by
        have h := hZ2 x hxZ2
        have ht4 : (t:ℝ)^((1:ℝ)/4) ≤ (x:ℝ)^((1:ℝ)/4) :=
          Real.rpow_le_rpow (by positivity) htle (by norm_num)
        have hl6 : (Real.log (2 * (N:ℝ) + 2)) ^ 6 ≤ (2 * Real.log x) ^ 6 :=
          pow_le_pow_left₀ (Real.log_nonneg (by linarith [show (0:ℝ) ≤ (N:ℝ) by positivity]))
            hlog2N2 6
        have h1 : CMd * (t:ℝ)^((1:ℝ)/4) * (Real.log (2 * (N:ℝ) + 2)) ^ 6
            ≤ CMd * (x:ℝ)^((1:ℝ)/4) * (2 * Real.log x)^6 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left ht4 hCMd.le) hl6 (by positivity)
            (by positivity)
        refine le_trans h1 ?_
        have h2 : CMd * (x:ℝ)^((1:ℝ)/4) * (2 * Real.log x)^6
            = CMd * 64 * (x:ℝ)^((1:ℝ)/4) * (Real.log x)^6 := by ring
        rw [h2]
        have hc := h
        rw [show (Real.log x) ^ ((6:ℝ)) = (Real.log x)^6 from Real.rpow_natCast _ 6] at hc
        simpa only [mul_assoc] using hc
      have hcA3 : 16 * Real.sqrt (N:ℝ)
          ≤ c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm)) := by
        have h := hZ3 x hxZ3
        refine le_trans (mul_le_mul_of_nonneg_left hsqrtN (by norm_num : (0:ℝ) ≤ 16)) ?_
        simpa only [mul_assoc] using h
      have hcA4 : 8 * Cinv
          ≤ c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm)) := by
        have h := hZ4 x hxZ4
        simpa only [Real.rpow_zero, mul_one, one_mul] using h
      have hcA5 : 4 * ((((⌊((t:ℝ)/16)^((1:ℝ)/4)⌋₊ : ℕ) : ℝ) + 1)
            * (Ct * (Real.log ((N:ℝ)+2))^4))
          ≤ c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm)) := by
        have h5 : 256 * Ct * ((x:ℝ)^((1:ℝ)/4) * (Real.log x)^4) ≤ (c1/2) * (x:ℝ)^((3:ℝ)/4)
            * (Real.log x) ^ ((-lamm)) := by
          have hc := hZ5 x hxZ5
          rw [show (Real.log x) ^ ((4:ℝ)) = (Real.log x)^4 from Real.rpow_natCast _ 4] at hc
          simpa only [mul_assoc] using hc
        have h6 : 256 * Ct * (Real.log x)^4 ≤ (c1/2) * (x:ℝ)^((3:ℝ)/4)
            * (Real.log x) ^ ((-lamm)) := by
          have hc := hZ6 x hxZ6
          rw [show (Real.log x) ^ ((4:ℝ)) = (Real.log x)^4 from Real.rpow_natCast _ 4] at hc
          simpa only [Real.rpow_zero, mul_one, mul_assoc] using hc
        have hl4 : (Real.log ((N:ℝ)+2))^4 ≤ 64 * (Real.log x)^4 := by
          have h1 : (Real.log ((N:ℝ)+2))^4 ≤ (2 * Real.log x)^4 :=
            pow_le_pow_left₀ (Real.log_nonneg (by linarith [show (0:ℝ) ≤ (N:ℝ) by positivity]))
              hlogNp2 4
          have h2 : (2 * Real.log x)^4 = 16 * (Real.log x)^4 := by ring
          have h3 : 16 * (Real.log x)^4 ≤ 64 * (Real.log x)^4 :=
            mul_le_mul_of_nonneg_right (by norm_num : (16:ℝ) ≤ 64) (pow_nonneg hlog0 4)
          linarith [h1, h2.le, h3]
        have h88 : 4 * ((((⌊((t:ℝ)/16)^((1:ℝ)/4)⌋₊ : ℕ) : ℝ) + 1)
              * (Ct * (Real.log ((N:ℝ)+2))^4))
            ≤ 256 * Ct * ((x:ℝ)^((1:ℝ)/4) * (Real.log x)^4)
              + 256 * Ct * (Real.log x)^4 := by
          have ha : 4 * ((((⌊((t:ℝ)/16)^((1:ℝ)/4)⌋₊ : ℕ) : ℝ) + 1)
                * (Ct * (Real.log ((N:ℝ)+2))^4))
              ≤ 4 * (((x:ℝ)^((1:ℝ)/4) + 1) * (Ct * (64 * (Real.log x)^4))) := by
            refine mul_le_mul le_rfl ?_ (by positivity) (by positivity)
            exact mul_le_mul hK16 (mul_le_mul_of_nonneg_left hl4 hCt.le) (by positivity)
              (by positivity)
          refine le_trans ha (le_of_eq ?_)
          ring
        have hsum2 : (c1/2) * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm))
              + (c1/2) * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm))
            ≤ c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm)) := le_of_eq (by ring)
        exact le_trans h88 (le_trans (add_le_add h5 h6) hsum2)
      have hcA6 : KK * (Real.log (N:ℝ))^M * (Real.sqrt (t:ℝ) + 1)
          ≤ 2 * (c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm))) := by
        have h8 : KK * K4 * (Real.log x)^M
            ≤ c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm)) := by
          simpa only [Real.rpow_zero, mul_one] using hZ8 x hxZ8
        have h7 : KK * K4 * (x:ℝ)^((1:ℝ)/2) * (Real.log x)^M
            ≤ c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm)) := hZ7 x hxZ7
        have hst : Real.sqrt (t:ℝ) ≤ (x:ℝ)^((1:ℝ)/2) := by
          rw [Real.sqrt_eq_rpow]
          exact Real.rpow_le_rpow (by positivity) htle (by norm_num)
        have h10 : (Real.log (N:ℝ))^M * (Real.sqrt (t:ℝ) + 1)
            ≤ (K4 * (Real.log x)^M) * ((x:ℝ)^((1:ℝ)/2) + 1) :=
          mul_le_mul hlogNM (by linarith) (by positivity) (by positivity)
        have h10' : KK * ((Real.log (N:ℝ))^M * (Real.sqrt (t:ℝ) + 1))
            ≤ KK * ((K4 * (Real.log x)^M) * ((x:ℝ)^((1:ℝ)/2) + 1)) :=
          mul_le_mul_of_nonneg_left h10 hKK0
        have hgoal1 : KK * (Real.log (N:ℝ))^M * (Real.sqrt (t:ℝ) + 1)
            ≤ KK * ((K4 * (Real.log x)^M) * ((x:ℝ)^((1:ℝ)/2) + 1)) := by
          simpa only [mul_assoc] using h10'
        refine le_trans hgoal1 ?_
        rw [show KK * ((K4 * (Real.log x)^M) * ((x:ℝ)^((1:ℝ)/2) + 1))
            = KK * K4 * (x:ℝ)^((1:ℝ)/2) * (Real.log x)^M + KK * K4 * (Real.log x)^M
            from by ring]
        have hsum2 : c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm))
              + c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm))
            ≤ 2 * (c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm))) := le_of_eq (by ring)
        exact le_trans (add_le_add h7 h8) hsum2
      have hmidA : 2 * (4 * (2 * Real.sqrt (N:ℝ) + Cinv)
            + 2 * ((((⌊((t:ℝ)/16)^((1:ℝ)/4)⌋₊ : ℕ) : ℝ) + 1)
              * (Ct * (Real.log ((N:ℝ)+2))^4)))
          ≤ 3 * (c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm))) := by
        set Z : ℝ := ((((⌊((t:ℝ)/16)^((1:ℝ)/4)⌋₊ : ℕ) : ℝ) + 1)
          * (Ct * (Real.log ((N:ℝ)+2))^4)) with hZdef
        have hZ5 : 4 * Z ≤ c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x) ^ ((-lamm)) := by
          rw [hZdef]; exact hcA5
        rw [show 2 * (4 * (2 * Real.sqrt (N:ℝ) + Cinv) + 2 * Z)
            = 16 * Real.sqrt (N:ℝ) + 8 * Cinv + 4 * Z from by ring]
        linarith [hcA3, hcA4, hZ5, hX0]
      have hT : (∑ p ∈ CO4 N, |(Submission.Ad (4 * (p.1 * p.2 ^ 2)) t : ℝ)
            - (Submission.gdens (4 * (p.1 * p.2 ^ 2)) : ℝ) * (Submission.Aseq t : ℝ)|)
          ≤ c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm))
            + c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm))
            + 3 * (c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm)))
            + 2 * (c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm))) := by
        linarith [hcf, hcA1, hcA2, hmidA, hcA6, hKKdef]
      have hS : (∑ d ∈ (Finset.range N).filter
            (fun d => (∀ p ∈ d.primeFactors, d.factorization p ≤ 2) ∧ 4 ∣ d),
            |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
          ≤ 1 + (c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm))
            + c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm))
            + 3 * (c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm)))
            + 2 * (c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm)))) :=
        le_trans hdd (add_le_add le_rfl hT)
      have hsumA : 1 + (c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm))
            + c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm))
            + 3 * (c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm)))
            + 2 * (c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm))))
          ≤ 16 * (c1 * (x:ℝ)^((3:ℝ)/4) * (Real.log x)^((-lamm))) := by
        linarith [he1, hX0]
      exact le_trans hS (le_trans hsumA hfin_16)
    · -- ## Case C: `N > t^{3/4}` (crude)
      have htN : (t:ℝ)^((3:ℝ)/4) ≤ 2 * (N:ℝ) := by
        have h1 : ((⌊(t:ℝ)^((3:ℝ)/4)⌋₊ : ℕ) : ℝ) ≤ (t:ℝ)^((3:ℝ)/4) := Nat.floor_le (by positivity)
        have h2 : (t:ℝ)^((3:ℝ)/4) < ((⌊(t:ℝ)^((3:ℝ)/4)⌋₊ : ℕ) : ℝ) + 1 :=
          Nat.lt_floor_add_one _
        have h3 : ((⌊(t:ℝ)^((3:ℝ)/4)⌋₊ : ℕ) : ℝ) < (N:ℝ) := by
          exact_mod_cast (Nat.lt_of_not_le hcase)
        have h4 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
        linarith
      exact hfin_crude (CO4_bound_crude N t (by omega) hCAd2.le hCAu.le hCg.le hAd2 hAu hAg3 ht2 htN)


/-- The `4 ∣ d` part of hypothesis `(R₃)` (the exponent `2^25` special case). -/
theorem R3_four_part : ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
    (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter
        (fun d => (∀ p ∈ d.primeFactors, d.factorization p ≤ 2) ∧ 4 ∣ d),
      |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
    ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-((2 : ℝ) ^ 25)) := by
  obtain ⟨X₀, hX₀⟩ := R3_four_part_generic ((2 : ℝ) ^ 25)
  exact ⟨X₀, fun x hx t ht2 htx => hX₀ x hx t ht2 htx⟩

end
end Submission.ASP

namespace Submission.ASP

open Finset

/-- **Hypothesis `(R₃)` for X²+Y⁴, for ALL cubefree moduli.**

The commons theorem `X2Y4_R3_hypothesis` gives `(R₃)` for the cubefree moduli not divisible by `4`,
and `R3_four_part` supplies the remaining ones (`4 ∣ d`); adding the two halves gives the full
cubefree sum, at the price of a factor `2` on the right hand side. -/
theorem X2Y4_R3_all : ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
    (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter
        (fun d => ∀ p ∈ d.primeFactors, d.factorization p ≤ 2),
      |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ 2 * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (-((2 : ℝ) ^ 25))) := by
  classical
  obtain ⟨X1, h1⟩ := R3_four_part
  obtain ⟨X2, h2⟩ := Commons.NumberTheory.FriedlanderIwaniec.X2Y4_R3_hypothesis
  refine ⟨max X1 X2, fun x hx t ht2 htx => ?_⟩
  have hx1 : X1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : X2 ≤ x := le_trans (le_max_right _ _) hx
  set s : Finset ℕ := (Finset.range (Submission.X2Y4R3.R3cut x)).filter
      (fun d => ∀ p ∈ d.primeFactors, d.factorization p ≤ 2) with hs
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun d => 4 ∣ d)
    (fun d => |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
  rw [← hsplit]
  have hp1 : (∑ d ∈ s.filter (fun d => 4 ∣ d),
        |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-((2 : ℝ) ^ 25)) := by
    rw [hs, Finset.filter_filter]
    exact h1 x hx1 t ht2 htx
  have hp2 : (∑ d ∈ s.filter (fun d => ¬ 4 ∣ d),
        |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-((2 : ℝ) ^ 25)) := by
    rw [hs, Finset.filter_filter, Submission.X2Y4R3.R3cut]
    exact h2 x hx2 t ht2 htx
  linarith [hp1, hp2]

/-- **Hypothesis `(R₃)` for X²+Y⁴, for ALL cubefree moduli, at an ARBITRARY log exponent.**
The two halves (`R3_four_part_generic` for `4 ∣ d` and `X2Y4_R3_generic` for `¬ 4 ∣ d`) each
saturate the budget, so the sum only pays a factor `2`. -/
theorem X2Y4_R3_all_generic (lamm : ℝ) : ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x → ∀ t : ℕ, 2 ≤ t → t ≤ x →
    (∑ d ∈ (Finset.range (Submission.X2Y4R3.R3cut x)).filter
        (fun d => ∀ p ∈ d.primeFactors, d.factorization p ≤ 2),
      |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ 2 * ((Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm)) := by
  classical
  obtain ⟨X1, h1⟩ := R3_four_part_generic lamm
  obtain ⟨X2, h2⟩ := Submission.X2Y4_R3_generic lamm
  refine ⟨max X1 X2, fun x hx t ht2 htx => ?_⟩
  have hx1 : X1 ≤ x := le_trans (le_max_left _ _) hx
  have hx2 : X2 ≤ x := le_trans (le_max_right _ _) hx
  set s : Finset ℕ := (Finset.range (Submission.X2Y4R3.R3cut x)).filter
      (fun d => ∀ p ∈ d.primeFactors, d.factorization p ≤ 2) with hs
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun d => 4 ∣ d)
    (fun d => |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
  rw [← hsplit]
  have hp1 : (∑ d ∈ s.filter (fun d => 4 ∣ d),
        |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
    rw [hs, Finset.filter_filter]
    exact h1 x hx1 t ht2 htx
  have hp2 : (∑ d ∈ s.filter (fun d => ¬ 4 ∣ d),
        |(Submission.Ad d t : ℝ) - (Submission.gdens d : ℝ) * (Submission.Aseq t : ℝ)|)
      ≤ (Submission.Aseq x : ℝ) * (Real.log x) ^ (-lamm) := by
    rw [hs, Finset.filter_filter, Submission.X2Y4R3.R3cut]
    exact h2 x hx2 t ht2 htx
  linarith [hp1, hp2]

end Submission.ASP
