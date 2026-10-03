import Mathlib
import Submission.Work.FIArea3.LargeUBase
import Submission.Work.FIArea3.tau_sq_trunc
import Submission.Work.FIArea3.JointCount.card_filter_le_le_arith
import Submission.Work.FIArea2.sum_tau_pow_le
import Submission.Work.FIArea2.sum_tau_pow_div_le

set_option maxHeartbeats 400000

namespace Work.FIArea3

open Finset Work.FIPlan
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

private lemma one_le_log_x_param (Pa : Work.FITop.Params) : 1 ≤ Real.log (Pa.x : ℝ) := by
  have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have h3 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_d9]
  exact le_trans h3 (Real.log_le_log (by norm_num) hx3)

private lemma theta_le_one_param (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  rw [Pa.hθ]
  refine Real.rpow_le_one_of_one_le_of_nonpos (one_le_log_x_param Pa) ?_
  linarith [Pa.hA', Pa.hA]

private lemma count_dvd_card_le (Pa : Work.FITop.Params) (φ : ℝ) (d : ℕ) (hd : 1 ≤ d) :
    (((polarBoxFinset Pa φ).filter (fun z => d ∣ gnorm z)).card : ℝ)
      ≤ Real.pi * (Pa.θ * Real.sqrt Pa.N) ^ 2 * ((d.divisors.card : ℝ) / (d : ℝ))
        + 80 * (Pa.θ * Real.sqrt Pa.N) * ((d.divisors.card : ℝ) / Real.sqrt (d : ℝ))
        + (d.divisors.card : ℝ) := by
  have h := JointCount.card_filter_le_le_arith Pa φ 0 d 1 hd le_rfl
  have heq : (polarBoxFinset Pa φ).filter (fun z => d ∣ gnorm z)
      = JointCount.pairBoxFinset Pa φ 0 d 1 := by
    rw [JointCount.pairBoxFinset]
    apply Finset.filter_congr
    intro z _
    simp
  rw [heq]; exact h

private lemma polarBox_tau_sq_le_sum (Pa : Work.FITop.Params) (φ : ℝ) (K : ℕ)
    (hK : ∀ z ∈ polarBoxFinset Pa φ, ((gnorm z : ℕ) : ℝ) ≤ (K : ℝ) ^ (4 : ℕ)) :
    (∑ z ∈ polarBoxFinset Pa φ, (((gnorm z).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
      ≤ (256 : ℝ) ^ (2 : ℕ) *
        ∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ) ^ (16 : ℕ)) *
          (((polarBoxFinset Pa φ).filter (fun z => d ∣ gnorm z)).card : ℝ) := by
  have h1 : (∑ z ∈ polarBoxFinset Pa φ, (((gnorm z).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
      ≤ ∑ z ∈ polarBoxFinset Pa φ, (256 : ℝ) ^ (2 : ℕ) * ∑ d ∈ Finset.Icc 1 K,
          (if d ∣ gnorm z then (((d.divisors.card : ℕ) : ℝ) ^ (16 : ℕ)) else 0) :=
    Finset.sum_le_sum (fun z hz => tau_sq_trunc (gnorm z) K (hK z hz))
  calc (∑ z ∈ polarBoxFinset Pa φ, (((gnorm z).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
      ≤ ∑ z ∈ polarBoxFinset Pa φ, (256 : ℝ) ^ (2 : ℕ) * ∑ d ∈ Finset.Icc 1 K,
          (if d ∣ gnorm z then (((d.divisors.card : ℕ) : ℝ) ^ (16 : ℕ)) else 0) := h1
    _ = (256 : ℝ) ^ (2 : ℕ) * ∑ z ∈ polarBoxFinset Pa φ, ∑ d ∈ Finset.Icc 1 K,
          (if d ∣ gnorm z then (((d.divisors.card : ℕ) : ℝ) ^ (16 : ℕ)) else 0) := by
        rw [Finset.mul_sum]
    _ = (256 : ℝ) ^ (2 : ℕ) * ∑ d ∈ Finset.Icc 1 K,
          ∑ z ∈ polarBoxFinset Pa φ,
          (if d ∣ gnorm z then (((d.divisors.card : ℕ) : ℝ) ^ (16 : ℕ)) else 0) := by
        rw [Finset.sum_comm]
    _ = (256 : ℝ) ^ (2 : ℕ) *
        ∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ) ^ (16 : ℕ)) *
          (((polarBoxFinset Pa φ).filter (fun z => d ∣ gnorm z)).card : ℝ) := by
        congr 1
        refine Finset.sum_congr rfl (fun d hd => ?_)
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

private theorem largeU_M2_arith_local :
    ∃ C : ℝ, 0 < C ∧
    ∀ (N u : ℝ) (K : ℕ), 1 ≤ N → 0 ≤ u → N ^ ((1:ℝ)/4) ≤ u →
      ((K : ℝ) ≤ 2 * (2 * N) ^ ((1:ℝ)/4)) →
      (∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ) ^ (16:ℕ))
          * (Real.pi * u ^ (2:ℕ) * (((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
             + 80 * u * (((d.divisors.card : ℕ) : ℝ) / Real.sqrt (d : ℝ))
             + ((d.divisors.card : ℕ) : ℝ)))
        ≤ C * u ^ (2:ℕ) * (2 + Real.log N) ^ (262144 : ℕ) := by
  obtain ⟨Cd, hCdpos, hCd⟩ := Work.FIArea2.sum_tau_pow_div_le 17
  refine ⟨200 * Cd, by positivity, ?_⟩
  intro N u K hN hu0 huN hK
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0
    have hemp : Finset.Icc 1 0 = (∅ : Finset ℕ) := by ext x; simp
    rw [hemp, Finset.sum_empty]
    positivity
  · have hK1R : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hKpos
    have hNpos : 0 < N := by linarith
    have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN
    have hL2 : (2:ℝ) ≤ 2 + Real.log N := by linarith
    have hN14le : N ^ ((1:ℝ)/4) ≤ N ^ ((1:ℝ)/2) :=
      Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
    have hN12le : N ^ ((1:ℝ)/2) ≤ u ^ (2:ℕ) := by
      have h := pow_le_pow_left₀ (Real.rpow_nonneg hNpos.le ((1:ℝ)/4)) huN 2
      have e : (N ^ ((1:ℝ)/4)) ^ (2:ℕ) = N ^ ((1:ℝ)/2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num
      rwa [e] at h
    have hKleN14 : (K:ℝ) ≤ 4 * N ^ ((1:ℝ)/4) := by
      have h1 : ((2*N):ℝ)^((1:ℝ)/4) = (2:ℝ)^((1:ℝ)/4) * N^((1:ℝ)/4) :=
        Real.mul_rpow (by norm_num) hNpos.le
      have h2 : (2:ℝ)^((1:ℝ)/4) ≤ 2 :=
        Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
      have h3 : (0:ℝ) ≤ N^((1:ℝ)/4) := Real.rpow_nonneg hNpos.le _
      have h4 : (2:ℝ)^((1:ℝ)/4) * N^((1:ℝ)/4) ≤ 2 * N^((1:ℝ)/4) :=
        mul_le_mul_of_nonneg_right h2 h3
      calc (K:ℝ) ≤ 2 * ((2*N):ℝ)^((1:ℝ)/4) := hK
        _ = 2 * ((2:ℝ)^((1:ℝ)/4) * N^((1:ℝ)/4)) := by rw [h1]
        _ ≤ 2 * (2 * N^((1:ℝ)/4)) := by linarith
        _ = 4 * N^((1:ℝ)/4) := by ring
    have hK4u2 : (K:ℝ) ≤ 4 * u ^ (2:ℕ) := by
      have hle : N ^ ((1:ℝ)/4) ≤ u^(2:ℕ) := le_trans hN14le hN12le
      linarith
    have hsqrtK : Real.sqrt (K:ℝ) ≤ 2*u := by
      rw [Real.sqrt_le_iff]
      exact ⟨by linarith, by nlinarith [hK4u2]⟩
    have hlog4 : Real.log 4 ≤ 2 := by
      rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
      push_cast
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
    have hlogK : Real.log (K:ℝ) ≤ Real.log 4 + (1/4) * Real.log N := by
      have h1 : Real.log (K:ℝ) ≤ Real.log (4 * N ^ ((1:ℝ)/4)) :=
        Real.log_le_log (by exact_mod_cast hKpos) hKleN14
      have h2 : Real.log (4 * N ^ ((1:ℝ)/4)) = Real.log 4 + (1:ℝ)/4 * Real.log N := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hNpos _).ne']
        rw [Real.log_rpow hNpos]
      linarith [h1, h2.le, h2.ge]
    have hlogK2 : Real.log (K:ℝ) + 2 ≤ 2 * (2 + Real.log N) := by
      linarith [hlogK, hlog4, hlogN0]
    have hpow_le : (Real.log (K:ℝ) + 2) ^ (2^17:ℕ) ≤ (2 + Real.log N)^(262144:ℕ) := by
      have hnn : 0 ≤ Real.log (K:ℝ) + 2 := by
        have := Real.log_nonneg hK1R; linarith
      have h1 : (Real.log (K:ℝ) + 2)^(2^17:ℕ) ≤ (2*(2+Real.log N))^(2^17:ℕ) :=
        pow_le_pow_left₀ hnn hlogK2 _
      have h3 : 2*(2+Real.log N) ≤ (2+Real.log N)^2 := by nlinarith only [hL2]
      have h2 : (2*(2+Real.log N))^(2^17:ℕ) ≤ (2+Real.log N)^(262144:ℕ) := by
        calc (2*(2+Real.log N))^(2^17:ℕ) ≤ ((2+Real.log N)^2)^(2^17:ℕ) :=
              pow_le_pow_left₀ (by positivity) h3 _
          _ = (2+Real.log N)^(262144:ℕ) := by rw [← pow_mul]; norm_num
      exact le_trans h1 h2
    set A : ℝ := ∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ) ^ (17:ℕ)) / (d : ℝ)
      with hAdef
    set B : ℝ := ∑ d ∈ Finset.Icc 1 K,
      (((d.divisors.card : ℕ) : ℝ) ^ (17:ℕ)) / Real.sqrt (d : ℝ) with hBdef
    set Ct : ℝ := ∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ) ^ (17:ℕ)) with hCtdef
    have hA0 : 0 ≤ A := by
      rw [hAdef]
      exact Finset.sum_nonneg
        fun d _ => div_nonneg (pow_nonneg (Nat.cast_nonneg _) 17) (Nat.cast_nonneg d)
    set X : ℝ := (2 + Real.log N)^(262144:ℕ) with hXdef
    have hX0 : 0 ≤ X := by
      rw [hXdef]; exact pow_nonneg (by linarith only [hlogN0]) _
    have hA_le : A ≤ Cd * (Real.log (K:ℝ) + 2)^(2^17:ℕ) := by
      rw [hAdef]; exact hCd K
    have hAfin : A ≤ Cd * X :=
      le_trans hA_le (mul_le_mul_of_nonneg_left hpow_le hCdpos.le)
    clear_value X A B Ct
    have hSsplit :
        (∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ) ^ (16:ℕ))
            * (Real.pi * u ^ (2:ℕ) * (((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
               + 80 * u * (((d.divisors.card : ℕ) : ℝ) / Real.sqrt (d : ℝ))
               + ((d.divisors.card : ℕ) : ℝ)))
          = Real.pi * u^2 * A + 80*u*B + Ct := by
      have hper : ∀ d : ℕ, (((d.divisors.card : ℕ) : ℝ) ^ (16:ℕ))
            * (Real.pi * u ^ (2:ℕ) * (((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
               + 80 * u * (((d.divisors.card : ℕ) : ℝ) / Real.sqrt (d : ℝ))
               + ((d.divisors.card : ℕ) : ℝ))
            = Real.pi * u^2 * (((d.divisors.card : ℕ) : ℝ) ^ (17:ℕ) / (d : ℝ))
              + 80*u*(((d.divisors.card : ℕ) : ℝ) ^ (17:ℕ) / Real.sqrt (d : ℝ))
              + (((d.divisors.card : ℕ) : ℝ) ^ (17:ℕ)) := by
        intro d; ring
      calc (∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ) ^ (16:ℕ))
            * (Real.pi * u ^ (2:ℕ) * (((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
               + 80 * u * (((d.divisors.card : ℕ) : ℝ) / Real.sqrt (d : ℝ))
               + ((d.divisors.card : ℕ) : ℝ)))
          = ∑ d ∈ Finset.Icc 1 K,
              (Real.pi * u^2 * (((d.divisors.card : ℕ) : ℝ) ^ (17:ℕ) / (d : ℝ))
              + 80*u*(((d.divisors.card : ℕ) : ℝ) ^ (17:ℕ) / Real.sqrt (d : ℝ))
              + (((d.divisors.card : ℕ) : ℝ) ^ (17:ℕ))) :=
              Finset.sum_congr rfl (fun d _ => hper d)
        _ = Real.pi * u^2 * A + 80*u*B + Ct := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                hAdef, hBdef, hCtdef, Finset.mul_sum, Finset.mul_sum]
    have hB_le : B ≤ Real.sqrt (K:ℝ) * A := by
      rw [hBdef, hAdef, Finset.mul_sum]
      refine Finset.sum_le_sum fun d hd => ?_
      obtain ⟨hd1, hdK⟩ := Finset.mem_Icc.mp hd
      have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
      have hs0 : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr hd0
      have hsq : Real.sqrt (d:ℝ) ≤ Real.sqrt (K:ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hdK)
      have hτ : (0:ℝ) ≤ (((d.divisors.card : ℕ) : ℝ) ^ (17:ℕ)) :=
        pow_nonneg (Nat.cast_nonneg _) 17
      have h1 : (1:ℝ) / Real.sqrt (d:ℝ) ≤ Real.sqrt (K:ℝ) / (d:ℝ) := by
        rw [div_le_div_iff₀ hs0 hd0]
        have hdd : (d:ℝ) = Real.sqrt (d:ℝ) * Real.sqrt (d:ℝ) :=
          (Real.mul_self_sqrt hd0.le).symm
        rw [hdd]
        simpa using mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg (d:ℝ))
      calc (((d.divisors.card : ℕ) : ℝ) ^ (17:ℕ)) / Real.sqrt (d:ℝ)
          = (((d.divisors.card : ℕ) : ℝ) ^ (17:ℕ)) * (1 / Real.sqrt (d:ℝ)) := by ring
        _ ≤ (((d.divisors.card : ℕ) : ℝ) ^ (17:ℕ)) * (Real.sqrt (K:ℝ) / (d:ℝ)) :=
              mul_le_mul_of_nonneg_left h1 hτ
        _ = Real.sqrt (K:ℝ) * ((((d.divisors.card : ℕ) : ℝ) ^ (17:ℕ)) / (d:ℝ)) := by ring
    have hCt_le : Ct ≤ (K:ℝ) * A := by
      rw [hCtdef, hAdef, Finset.mul_sum]
      refine Finset.sum_le_sum fun d hd => ?_
      obtain ⟨hd1, hdK⟩ := Finset.mem_Icc.mp hd
      have hd0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
      have hdK' : (d:ℝ) ≤ (K:ℝ) := by exact_mod_cast hdK
      have hτ : (0:ℝ) ≤ (((d.divisors.card : ℕ) : ℝ) ^ (17:ℕ)) :=
        pow_nonneg (Nat.cast_nonneg _) 17
      rw [← mul_div_assoc]
      rw [le_div_iff₀ hd0]
      linarith only [mul_le_mul_of_nonneg_left hdK' hτ]
    have hS_le : (∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ) ^ (16:ℕ))
            * (Real.pi * u ^ (2:ℕ) * (((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
               + 80 * u * (((d.divisors.card : ℕ) : ℝ) / Real.sqrt (d : ℝ))
               + ((d.divisors.card : ℕ) : ℝ)))
          ≤ (Real.pi + 164) * u^2 * A := by
      have h1 : 80*u*B ≤ 160*u^2*A := by
        calc 80*u*B ≤ 80*u*((2*u)*A) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact le_trans hB_le (mul_le_mul_of_nonneg_right hsqrtK hA0)
          _ = 160*u^2*A := by ring
      have h2 : Ct ≤ 4*u^2*A := le_trans hCt_le (mul_le_mul_of_nonneg_right hK4u2 hA0)
      rw [hSsplit]
      linarith only [h1, h2]
    have hS_fin : (∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ) ^ (16:ℕ))
            * (Real.pi * u ^ (2:ℕ) * (((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
               + 80 * u * (((d.divisors.card : ℕ) : ℝ) / Real.sqrt (d : ℝ))
               + ((d.divisors.card : ℕ) : ℝ)))
          ≤ 200 * Cd * u^2 * X := by
      have hπ : Real.pi + 164 ≤ 200 := by linarith only [Real.pi_lt_four]
      calc (∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ) : ℝ) ^ (16:ℕ))
            * (Real.pi * u ^ (2:ℕ) * (((d.divisors.card : ℕ) : ℝ) / (d : ℝ))
               + 80 * u * (((d.divisors.card : ℕ) : ℝ) / Real.sqrt (d : ℝ))
               + ((d.divisors.card : ℕ) : ℝ)))
          ≤ (Real.pi + 164) * u^2 * A := hS_le
        _ ≤ (Real.pi + 164) * u^2 * (Cd * X) :=
            mul_le_mul_of_nonneg_left hAfin (by positivity)
        _ = (Real.pi + 164) * (u^2 * Cd * X) := by ring
        _ ≤ 200 * (u^2 * Cd * X) :=
            mul_le_mul_of_nonneg_right hπ (mul_nonneg (mul_nonneg (sq_nonneg u) hCdpos.le) hX0)
        _ = 200 * Cd * u^2 * X := by ring
    exact hS_fin

theorem largeU_M2 : ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ),
      Pa.N ^ ((1 : ℝ) / 4) ≤ Pa.θ * Real.sqrt Pa.N →
      (∑ z ∈ Work.FIArea3.polarBoxFinset Pa φ,
          (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ^ (2 : ℕ))
        ≤ C * (Pa.θ * Real.sqrt Pa.N) ^ (2 : ℕ) * (2 + Real.log Pa.N) ^ (262144 : ℕ) := by
  obtain ⟨C2, hC2pos, hC2⟩ := largeU_M2_arith_local
  refine ⟨(256:ℝ)^2 * C2, by positivity, ?_⟩
  intro Pa φ hu
  set u : ℝ := Pa.θ * Real.sqrt Pa.N with hu_def
  set K : ℕ := ⌈(2 * Pa.N) ^ ((1:ℝ)/4)⌉₊ with hKdef
  have hN1 : (1:ℝ) ≤ Pa.N := by exact_mod_cast Pa.hN1
  have hNpos : (0:ℝ) < Pa.N := by linarith
  have hu0 : 0 ≤ u := by rw [hu_def]; exact mul_nonneg Pa.hθ0.le (Real.sqrt_nonneg _)
  have hu_hyp : Pa.N ^ ((1:ℝ)/4) ≤ u := by rw [hu_def]; exact hu
  have hθ1 : Pa.θ ≤ 1 := theta_le_one_param Pa
  have h2N0 : (0:ℝ) ≤ 2 * Pa.N := by linarith
  have hrp0 : (0:ℝ) ≤ (2 * Pa.N) ^ ((1:ℝ)/4) := Real.rpow_nonneg h2N0 _
  have hceil : (2 * Pa.N) ^ ((1:ℝ)/4) ≤ (K:ℝ) := by rw [hKdef]; exact Nat.le_ceil _
  have h2N1 : (1:ℝ) ≤ (2*Pa.N)^((1:ℝ)/4) := Real.one_le_rpow (by linarith) (by norm_num)
  have hKle : (K:ℝ) ≤ 2 * (2 * Pa.N)^((1:ℝ)/4) := by
    have hlt : (K:ℝ) < (2*Pa.N)^((1:ℝ)/4) + 1 := by
      rw [hKdef]; exact Nat.ceil_lt_add_one hrp0
    linarith
  have hK4 : 2 * Pa.N ≤ (K:ℝ)^4 := by
    calc 2 * Pa.N = ((2*Pa.N)^((1:ℝ)/4))^4 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul h2N0]
          norm_num
       _ ≤ (K:ℝ)^4 := pow_le_pow_left₀ hrp0 hceil 4
  have hKz : ∀ z ∈ polarBoxFinset Pa φ, ((gnorm z : ℕ) : ℝ) ≤ (K:ℝ)^4 := by
    intro z hz
    obtain ⟨-, hzin⟩ := mem_polarBoxFinset.mp hz
    have hle : ((gnorm z : ℕ) : ℝ) ≤ (1 + Pa.θ) * Pa.N := hzin.2.2.1
    have h2 : (1 + Pa.θ) * Pa.N ≤ 2 * Pa.N := by nlinarith [hθ1, hNpos.le]
    linarith
  have hstep1 := polarBox_tau_sq_le_sum Pa φ K hKz
  have hcount : ∀ d ∈ Finset.Icc 1 K,
      (((polarBoxFinset Pa φ).filter (fun z => d ∣ gnorm z)).card : ℝ)
        ≤ Real.pi * u^2 * ((d.divisors.card : ℝ)/(d:ℝ))
          + 80*u*((d.divisors.card : ℝ)/Real.sqrt (d:ℝ)) + (d.divisors.card : ℝ) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have h := count_dvd_card_le Pa φ d hd1
    rw [← hu_def] at h
    exact h
  have hstep2 : (∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ):ℝ)^(16:ℕ)) *
        (((polarBoxFinset Pa φ).filter (fun z => d ∣ gnorm z)).card : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ):ℝ)^(16:ℕ)) *
        (Real.pi * u^2 * ((d.divisors.card : ℝ)/(d:ℝ))
          + 80*u*((d.divisors.card : ℝ)/Real.sqrt (d:ℝ)) + (d.divisors.card : ℝ)) :=
    Finset.sum_le_sum (fun d hd => mul_le_mul_of_nonneg_left (hcount d hd)
      (pow_nonneg (Nat.cast_nonneg _) 16))
  have harith := hC2 Pa.N u K hN1 hu0 hu_hyp hKle
  calc (∑ z ∈ polarBoxFinset Pa φ, (((gnorm z).divisors.card : ℕ) : ℝ) ^ (2:ℕ))
      ≤ (256:ℝ)^2 * ∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ):ℝ)^(16:ℕ)) *
          (((polarBoxFinset Pa φ).filter (fun z => d ∣ gnorm z)).card : ℝ) := hstep1
    _ ≤ (256:ℝ)^2 * ∑ d ∈ Finset.Icc 1 K, (((d.divisors.card : ℕ):ℝ)^(16:ℕ)) *
          (Real.pi * u^2 * ((d.divisors.card : ℝ)/(d:ℝ))
            + 80*u*((d.divisors.card : ℝ)/Real.sqrt (d:ℝ)) + (d.divisors.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hstep2 (by positivity)
    _ ≤ (256:ℝ)^2 * (C2 * u^2 * (2 + Real.log Pa.N)^(262144:ℕ)) :=
        mul_le_mul_of_nonneg_left harith (by positivity)
    _ = (256:ℝ)^2 * C2 * u^2 * (2 + Real.log Pa.N)^(262144:ℕ) := by
        simp only [mul_assoc]

end

end Work.FIArea3
