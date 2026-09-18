import Mathlib
import Submission.Commons.NumberTheory.Mertens.mertens_lower
import Submission.Commons.NumberTheory.Mertens.legendre_sum_identity
import Submission.Commons.NumberTheory.Mertens.logDiv_ge_log_sub_sharp
import Submission.Commons.NumberTheory.Mertens.primeRecips_loglog_diff
import Submission.Commons.NumberTheory.Chebyshev.theta_le_log3_mul
import Submission.Commons.Analysis.SpecialFunctions.Log.log_factorial_sub_bounds
import Submission.Commons.NumberTheory.Mertens.sum_log_prime_ratio_real_tendsto
import Submission.Commons.NumberTheory.Mertens.corr_partial_sums_tendsto_tsum
import Submission.Commons.NumberTheory.Mertens.corr_sum_le

set_option maxRecDepth 100000

namespace Commons.NumberTheory.Mertens

open Finset Real MeasureTheory
open scoped BigOperators

noncomputable section



private lemma log2_ub : Real.log 2 ≤ (0.6931471808 : ℝ) := le_of_lt Real.log_two_lt_d9
private lemma log3_ub : Real.log 3 ≤ (1.0986122888 : ℝ) := le_of_lt Real.log_three_lt_d9

private lemma theta_real_le (t : ℝ) (ht : 0 ≤ t) : Chebyshev.theta t ≤ Real.log 3 * t := by
  have hfloor : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  calc Chebyshev.theta t = Chebyshev.theta ((⌊t⌋₊ : ℕ) : ℝ) := Chebyshev.theta_eq_theta_coe_floor t
    _ ≤ Real.log 3 * ((⌊t⌋₊ : ℕ) : ℝ) := Commons.NumberTheory.Chebyshev.theta_le_log3_mul ⌊t⌋₊
    _ ≤ Real.log 3 * t := mul_le_mul_of_nonneg_left hfloor hlog3

private lemma nat_div_pred (n p : ℕ) (hp0 : 0 < p) : n < (n / p + 1) * p := by
  have h2 : n % p < p := Nat.mod_lt _ hp0
  calc n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
    _ < p * (n / p) + p := Nat.add_lt_add_left h2 _
    _ = (n / p + 1) * p := by ring

private lemma nat_le_two_div_add_one (n : ℕ) : n ≤ 2 * (n / 2) + 1 := by
  have h1 := Nat.div_add_mod n 2
  have h2 : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
  omega

private lemma two_le_nat_div (n : ℕ) (hn : 4 ≤ n) : 2 ≤ n / 2 := by
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  omega

/-- The fractional-part sum of Legendre's formula is at most `0.765 n`. -/
private lemma fracSum_le (n : ℕ) (hn : 1000 ≤ n) :
    (∑ p ∈ n.primesLE,
        (((n : ℝ) / (p : ℝ)) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ)) ≤ 0.765 * (n : ℝ) := by
  set m : ℕ := n / 2 with hm
  have hmn : m ≤ n := Nat.div_le_self n 2
  have hm2 : 2 ≤ m := by rw [hm]; exact two_le_nat_div n (by omega)
  have hm500 : (500 : ℝ) ≤ (m : ℝ) := by
    have : 500 ≤ m := by rw [hm]; rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]; omega
    exact_mod_cast this
  have hsub : m.primesLE ⊆ n.primesLE := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 hmn, hp.2⟩
  let F : ℕ → ℝ := fun p => (((n : ℝ) / (p : ℝ)) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ)
  have hsplit := Finset.sum_sdiff hsub (f := F)
  have hsplit' : (∑ p ∈ n.primesLE, F p)
      = (∑ p ∈ m.primesLE, F p) + ∑ p ∈ n.primesLE \ m.primesLE, F p := by linarith
  -- Part A
  have hA : (∑ p ∈ m.primesLE, F p) ≤ Chebyshev.theta (m : ℝ) := by
    have hbound : ∀ p ∈ m.primesLE, F p ≤ Real.log (p : ℝ) := by
      intro p hp
      have hpP : p.Prime := Nat.prime_of_mem_primesLE hp
      have hp2 : 2 ≤ p := hpP.two_le
      have hp0n : 0 < p := by omega
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0n
      have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by
        have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
        linarith)
      have hfrac : ((n : ℝ) / (p : ℝ)) - ((n / p : ℕ) : ℝ) ≤ 1 := by
        have hnat := nat_div_pred n p hp0n
        have hreal : (n : ℝ) < (((n / p + 1) * p : ℕ) : ℝ) := by exact_mod_cast hnat
        push_cast at hreal
        have := (div_lt_iff₀ hp0).mpr hreal
        linarith
      simp only [F]
      calc (((n : ℝ) / (p : ℝ)) - ((n / p : ℕ) : ℝ)) * Real.log (p : ℝ)
          ≤ 1 * Real.log (p : ℝ) := mul_le_mul_of_nonneg_right hfrac hlogp
        _ = Real.log (p : ℝ) := one_mul _
    calc (∑ p ∈ m.primesLE, F p)
        ≤ ∑ p ∈ m.primesLE, Real.log (p : ℝ) := Finset.sum_le_sum hbound
      _ = Chebyshev.theta (m : ℝ) := (Chebyshev.theta_eq_sum_primesLE_log m).symm
  -- Part B
  have hB : (∑ p ∈ n.primesLE \ m.primesLE, F p)
      = (n : ℝ) * (logDiv (n : ℝ) - logDiv (m : ℝ))
        - (Chebyshev.theta (n : ℝ) - Chebyshev.theta (m : ℝ)) := by
    have hterm : ∀ p ∈ n.primesLE \ m.primesLE,
        F p = (n : ℝ) * (Real.log (p : ℝ) / (p : ℝ)) - Real.log (p : ℝ) := by
      intro p hp
      rw [Finset.mem_sdiff] at hp
      obtain ⟨hpn, hpm⟩ := hp
      rw [Nat.mem_primesLE] at hpn
      have hpP : p.Prime := hpn.2
      have hpnle : p ≤ n := hpn.1
      have hp0n : 0 < p := hpP.pos
      have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0n
      have hmp : m < p := by
        by_contra hc
        exact hpm (Nat.mem_primesLE.mpr ⟨not_lt.mp hc, hpP⟩)
      have h2p : n < 2 * p := by
        have h := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2)).mp (by rw [← hm]; exact hmp)
        omega
      have hdiv : n / p = 1 := Nat.div_eq_of_lt_le (k := 1) (n := p) (m := n)
        (by simpa using hpnle) (by simpa using h2p)
      simp only [F]
      rw [hdiv]
      push_cast
      have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
      field_simp
      try ring
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_sub_distrib]
    congr 1
    · rw [← Finset.mul_sum]
      have h1 : (∑ p ∈ n.primesLE \ m.primesLE, Real.log (p : ℝ) / (p : ℝ))
          = (∑ p ∈ n.primesLE, Real.log (p : ℝ) / (p : ℝ))
            - ∑ p ∈ m.primesLE, Real.log (p : ℝ) / (p : ℝ) := by
        have h := Finset.sum_sdiff hsub (f := (fun p : ℕ => Real.log (p : ℝ) / (p : ℝ)))
        linarith
      have h2 : (∑ p ∈ n.primesLE, Real.log (p : ℝ) / (p : ℝ)) = logDiv (n : ℝ) := by
        unfold logDiv; rw [Nat.floor_natCast]
      have h3 : (∑ p ∈ m.primesLE, Real.log (p : ℝ) / (p : ℝ)) = logDiv (m : ℝ) := by
        unfold logDiv; rw [Nat.floor_natCast]
      rw [h1, h2, h3]
    · have h1 : (∑ p ∈ n.primesLE \ m.primesLE, Real.log (p : ℝ))
          = (∑ p ∈ n.primesLE, Real.log (p : ℝ)) - ∑ p ∈ m.primesLE, Real.log (p : ℝ) := by
        have h := Finset.sum_sdiff hsub (f := (fun p : ℕ => Real.log (p : ℝ)))
        linarith
      have h2 : (∑ p ∈ n.primesLE, Real.log (p : ℝ)) = Chebyshev.theta (n : ℝ) :=
        (Chebyshev.theta_eq_sum_primesLE_log n).symm
      have h3 : (∑ p ∈ m.primesLE, Real.log (p : ℝ)) = Chebyshev.theta (m : ℝ) :=
        (Chebyshev.theta_eq_sum_primesLE_log m).symm
      rw [h1, h2, h3]
  -- Abel identities
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
  have hm2R : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hAbel_N : logDiv (n : ℝ)
      = Chebyshev.theta (n : ℝ) / (n : ℝ)
        + ∫ t in (2 : ℝ)..(n : ℝ), Chebyshev.theta t / (t * t) :=
    logDiv_eq_theta_div_add_integral hn2
  have hAbel_M : logDiv (m : ℝ)
      = Chebyshev.theta (m : ℝ) / (m : ℝ)
        + ∫ t in (2 : ℝ)..(m : ℝ), Chebyshev.theta t / (t * t) :=
    logDiv_eq_theta_div_add_integral hm2R
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have hm0 : (0 : ℝ) < (m : ℝ) := by positivity
  have hInt_split : (∫ t in (2:ℝ)..(n:ℝ), Chebyshev.theta t / (t * t))
      = (∫ t in (2:ℝ)..(m:ℝ), Chebyshev.theta t / (t * t))
        + ∫ t in (m:ℝ)..(n:ℝ), Chebyshev.theta t / (t * t) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_theta_div_id_sq_gen (by norm_num : (2:ℝ) ≤ 2) hm2R)
      (intervalIntegrable_theta_div_id_sq_gen hm2R hmnR)).symm
  have hkey : Chebyshev.theta (m:ℝ)
      + ((n:ℝ) * (logDiv (n:ℝ) - logDiv (m:ℝ)) - (Chebyshev.theta (n:ℝ) - Chebyshev.theta (m:ℝ)))
      = (2 - (n : ℝ) / (m : ℝ)) * Chebyshev.theta (m : ℝ)
        + (n : ℝ) * ∫ t in (m:ℝ)..(n:ℝ), Chebyshev.theta t / (t * t) := by
    rw [hAbel_N, hAbel_M, hInt_split]
    have hmne : (m:ℝ) ≠ 0 := ne_of_gt hm0
    field_simp
    ring
  have hmain : (∑ p ∈ n.primesLE, F p)
      ≤ (2 - (n : ℝ) / (m : ℝ)) * Chebyshev.theta (m : ℝ)
        + (n : ℝ) * ∫ t in (m:ℝ)..(n:ℝ), Chebyshev.theta t / (t * t) := by
    calc (∑ p ∈ n.primesLE, F p)
        = (∑ p ∈ m.primesLE, F p) + ∑ p ∈ n.primesLE \ m.primesLE, F p := hsplit'
      _ ≤ Chebyshev.theta (m:ℝ) + ((n:ℝ) * (logDiv (n:ℝ) - logDiv (m:ℝ))
            - (Chebyshev.theta (n:ℝ) - Chebyshev.theta (m:ℝ))) :=
          add_le_add hA (le_of_eq hB)
      _ = _ := hkey
  have hnm2 : 2 ≤ (n:ℝ)/(m:ℝ) := by
    rw [le_div_iff₀ hm0]
    have : (m:ℝ) * 2 ≤ (n:ℝ) := by
      rw [hm]; exact_mod_cast Nat.div_mul_le_self n 2
    linarith
  have hthm : 0 ≤ Chebyshev.theta (m:ℝ) := Chebyshev.theta_nonneg (m:ℝ)
  have hIntle : (∫ t in (m:ℝ)..(n:ℝ), Chebyshev.theta t / (t * t))
      ≤ Real.log 3 * Real.log ((n:ℝ)/(m:ℝ)) := by
    have hcont : IntervalIntegrable (fun t : ℝ => Real.log 3 * t⁻¹) volume (m:ℝ) (n:ℝ) := by
      apply ContinuousOn.intervalIntegrable
      intro z hz
      have hz0 : z ≠ 0 := by
        rw [Set.uIcc_of_le hmnR] at hz
        linarith [hz.1]
      exact (continuousAt_const.mul (continuousAt_id.inv₀ hz0)).continuousWithinAt
    have hmono := intervalIntegral.integral_mono_on hmnR
      (intervalIntegrable_theta_div_id_sq_gen hm2R hmnR) hcont ?_
    · rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hm0 hn0] at hmono
      exact hmono
    · intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      have h := theta_real_le t ht0.le
      have hden : 0 < t * t := by positivity
      rw [div_le_iff₀ hden]
      have htne : t ≠ 0 := ne_of_gt ht0
      have hgoal : Real.log 3 * t⁻¹ * (t*t) = Real.log 3 * t := by field_simp
      rw [hgoal]
      exact h
  have hlogratio : Real.log ((n:ℝ)/(m:ℝ)) ≤ Real.log 2 + 1/(2*(m:ℝ)) := by
    have hnm_le : (n:ℝ)/(m:ℝ) ≤ 2 + 1/(m:ℝ) := by
      rw [div_le_iff₀ hm0]
      have hgoal : (2 + 1/(m:ℝ)) * (m:ℝ) = 2*(m:ℝ) + 1 := by field_simp
      have hnn : (n:ℝ) ≤ 2*(m:ℝ) + 1 := by
        have h := nat_le_two_div_add_one n
        rw [← hm] at h
        exact_mod_cast h
      rw [hgoal]
      exact hnn
    have h2 : Real.log ((n:ℝ)/(m:ℝ)) ≤ Real.log (2 + 1/(m:ℝ)) :=
      Real.log_le_log (by positivity) hnm_le
    have h3 : Real.log (2 + 1/(m:ℝ)) = Real.log 2 + Real.log (1 + 1/(2*(m:ℝ))) := by
      have : (2:ℝ) + 1/(m:ℝ) = 2 * (1 + 1/(2*(m:ℝ))) := by field_simp; try ring
      rw [this, Real.log_mul (by norm_num) (by positivity)]
    have h4 : Real.log (1 + 1/(2*(m:ℝ))) ≤ 1/(2*(m:ℝ)) := by
      have hpos : (0:ℝ) < 1/(2*(m:ℝ)) := by positivity
      have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + 1/(2*(m:ℝ)))
      linarith
    calc Real.log ((n:ℝ)/(m:ℝ)) ≤ Real.log (2 + 1/(m:ℝ)) := h2
      _ = Real.log 2 + Real.log (1 + 1/(2*(m:ℝ))) := h3
      _ ≤ Real.log 2 + 1/(2*(m:ℝ)) := by linarith [h4]
  have hfinal : (2 - (n:ℝ)/(m:ℝ)) * Chebyshev.theta (m:ℝ) ≤ 0 := by
    have h1 : (2:ℝ) - (n:ℝ)/(m:ℝ) ≤ 0 := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg h1 hthm
  have hInt2 : (n:ℝ) * ∫ t in (m:ℝ)..(n:ℝ), Chebyshev.theta t / (t * t)
      ≤ (n:ℝ) * (Real.log 3 * (Real.log 2 + 1/(2*(m:ℝ)))) := by
    have hn' : (0:ℝ) ≤ (n:ℝ) := le_of_lt hn0
    calc (n:ℝ) * ∫ t in (m:ℝ)..(n:ℝ), Chebyshev.theta t / (t * t)
        ≤ (n:ℝ) * (Real.log 3 * Real.log ((n:ℝ)/(m:ℝ))) :=
          mul_le_mul_of_nonneg_left hIntle hn'
      _ ≤ (n:ℝ) * (Real.log 3 * (Real.log 2 + 1/(2*(m:ℝ)))) := by
          apply mul_le_mul_of_nonneg_left _ hn'
          exact mul_le_mul_of_nonneg_left hlogratio (Real.log_nonneg (by norm_num))
  have hnum : (n:ℝ) * (Real.log 3 * (Real.log 2 + 1/(2*(m:ℝ)))) ≤ 0.765 * (n:ℝ) := by
    have hrec : 1/(2*(m:ℝ)) ≤ 1/1000 := by
      apply one_div_le_one_div_of_le (by norm_num)
      linarith
    have hprod : (1.0986122888:ℝ) * (0.6931471808 + 1/1000) ≤ 0.765 := by norm_num
    have hbnd : Real.log 3 * (Real.log 2 + 1/(2*(m:ℝ))) ≤ (1.0986122888:ℝ) * (0.6931471808 + 1/1000) := by
      have h1 : Real.log 2 + 1/(2*(m:ℝ)) ≤ (0.6931471808:ℝ) + 1/1000 := by
        linarith [log2_ub, hrec]
      have h2 := mul_le_mul log3_ub h1 (by positivity) (by norm_num : (0:ℝ) ≤ 1.0986122888)
      linarith [h2]
    calc (n:ℝ) * (Real.log 3 * (Real.log 2 + 1/(2*(m:ℝ))))
        ≤ (n:ℝ) * ((1.0986122888:ℝ) * (0.6931471808 + 1/1000)) :=
          mul_le_mul_of_nonneg_left hbnd (le_of_lt hn0)
      _ ≤ (n:ℝ) * 0.765 := mul_le_mul_of_nonneg_left hprod (le_of_lt hn0)
      _ = 0.765 * (n:ℝ) := by ring
  linarith [hmain, hfinal, hInt2, hnum]



private lemma log2_lb : (0.6931471803 : ℝ) ≤ Real.log 2 := le_of_lt Real.log_two_gt_d9
private lemma log3_lb : (1.0986122885 : ℝ) ≤ Real.log 3 := le_of_lt Real.log_three_gt_d9
private lemma log5_lb : (1.6094379123 : ℝ) ≤ Real.log 5 := le_of_lt Real.log_five_gt_d9

private lemma log7_lb : (1.9365843 : ℝ) ≤ Real.log 7 := by
  have h8 : (0 : ℝ) < 8 / 7 := by norm_num
  have h := Real.log_le_sub_one_of_pos h8
  rw [Real.log_div (by norm_num) (by norm_num)] at h
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [hlog8] at h
  linarith

private lemma div_ge_sub_one (n k : ℕ) (hk : 0 < k) : (n : ℝ)/k - 1 ≤ ((n / k : ℕ) : ℝ) := by
  have h2 : n = k * (n / k) + n % k := (Nat.div_add_mod n k).symm
  have h3 : n % k < k := Nat.mod_lt _ hk
  have h4 : (n : ℝ) = (k : ℝ) * ((n / k : ℕ) : ℝ) + ((n % k : ℕ) : ℝ) := by
    have hcast := congrArg (fun m : ℕ => (m : ℝ)) h2
    push_cast at hcast
    linarith [hcast]
  have h5 : ((n % k : ℕ) : ℝ) < (k : ℝ) := by exact_mod_cast h3
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have : (n : ℝ) / (k : ℝ) < ((n / k : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hk0]
    linarith [h4, h5]
  linarith

private lemma inner_two_ge (n : ℕ) (hn : 100 ≤ n) :
    0.484375 * (n:ℝ) - 5 ≤ (∑ i ∈ Finset.Ico 2 (n + 1), ((n / 2 ^ i : ℕ) : ℝ)) := by
  have hsub : Finset.Ico 2 7 ⊆ Finset.Ico 2 (n + 1) := by
    intro i hi
    rw [Finset.mem_Ico] at hi ⊢
    exact ⟨hi.1, by omega⟩
  have hmono : (∑ i ∈ Finset.Ico 2 7, ((n / 2 ^ i : ℕ) : ℝ))
      ≤ (∑ i ∈ Finset.Ico 2 (n + 1), ((n / 2 ^ i : ℕ) : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
  have hset : Finset.Ico 2 7 = ({2,3,4,5,6} : Finset ℕ) := by decide
  have hval : (∑ i ∈ Finset.Ico 2 7, ((n / 2 ^ i : ℕ) : ℝ))
      = ((n/4:ℕ):ℝ) + ((n/8:ℕ):ℝ) + ((n/16:ℕ):ℝ) + ((n/32:ℕ):ℝ) + ((n/64:ℕ):ℝ) := by
    rw [hset]
    norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
    ring
  rw [hval] at hmono
  have h4 := div_ge_sub_one n 4 (by norm_num)
  have h8 := div_ge_sub_one n 8 (by norm_num)
  have h16 := div_ge_sub_one n 16 (by norm_num)
  have h32 := div_ge_sub_one n 32 (by norm_num)
  have h64 := div_ge_sub_one n 64 (by norm_num)
  linarith

private lemma inner_three_ge (n : ℕ) (hn : 100 ≤ n) :
    0.1604938271 * (n:ℝ) - 3 ≤ (∑ i ∈ Finset.Ico 2 (n + 1), ((n / 3 ^ i : ℕ) : ℝ)) := by
  have hsub : Finset.Ico 2 5 ⊆ Finset.Ico 2 (n + 1) := by
    intro i hi
    rw [Finset.mem_Ico] at hi ⊢
    exact ⟨hi.1, by omega⟩
  have hmono : (∑ i ∈ Finset.Ico 2 5, ((n / 3 ^ i : ℕ) : ℝ))
      ≤ (∑ i ∈ Finset.Ico 2 (n + 1), ((n / 3 ^ i : ℕ) : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
  have hset : Finset.Ico 2 5 = ({2,3,4} : Finset ℕ) := by decide
  have hval : (∑ i ∈ Finset.Ico 2 5, ((n / 3 ^ i : ℕ) : ℝ))
      = ((n/9:ℕ):ℝ) + ((n/27:ℕ):ℝ) + ((n/81:ℕ):ℝ) := by
    rw [hset]
    norm_num [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton]
    ring
  rw [hval] at hmono
  have h9 := div_ge_sub_one n 9 (by norm_num)
  have h27 := div_ge_sub_one n 27 (by norm_num)
  have h81 := div_ge_sub_one n 81 (by norm_num)
  linarith

private lemma inner_five_ge (n : ℕ) (hn : 100 ≤ n) :
    0.04 * (n:ℝ) - 1 ≤ (∑ i ∈ Finset.Ico 2 (n + 1), ((n / 5 ^ i : ℕ) : ℝ)) := by
  have h2 : 2 ∈ Finset.Ico 2 (n + 1) := by
    rw [Finset.mem_Ico]; exact ⟨le_rfl, by omega⟩
  have hnonneg : ∀ i ∈ Finset.Ico 2 (n+1), (0:ℝ) ≤ ((n / 5 ^ i : ℕ) : ℝ) :=
    fun i _ => by positivity
  have hsingle := Finset.single_le_sum hnonneg h2
  have hv : ((n / 5 ^ 2 : ℕ) : ℝ) = ((n/25:ℕ):ℝ) := by norm_num
  rw [hv] at hsingle
  have h25 := div_ge_sub_one n 25 (by norm_num)
  linarith

private lemma inner_seven_ge (n : ℕ) (hn : 100 ≤ n) :
    0.0204081632 * (n:ℝ) - 1 ≤ (∑ i ∈ Finset.Ico 2 (n + 1), ((n / 7 ^ i : ℕ) : ℝ)) := by
  have h2 : 2 ∈ Finset.Ico 2 (n + 1) := by
    rw [Finset.mem_Ico]; exact ⟨le_rfl, by omega⟩
  have hnonneg : ∀ i ∈ Finset.Ico 2 (n+1), (0:ℝ) ≤ ((n / 7 ^ i : ℕ) : ℝ) :=
    fun i _ => by positivity
  have hsingle := Finset.single_le_sum hnonneg h2
  have hv : ((n / 7 ^ 2 : ℕ) : ℝ) = ((n/49:ℕ):ℝ) := by norm_num
  rw [hv] at hsingle
  have h49 := div_ge_sub_one n 49 (by norm_num)
  linarith

private lemma tailSum_ge (n : ℕ) (hn : 100 ≤ n) :
    0.6159 * (n : ℝ) - 10.32 ≤
      (∑ p ∈ n.primesLE, (∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ)) := by
  have hsub : ({2,3,5,7} : Finset ℕ) ⊆ n.primesLE := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      exact Nat.mem_primesLE.mpr ⟨by omega, by decide⟩
  have hnonneg : ∀ p ∈ n.primesLE,
      0 ≤ (∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ) := by
    intro p hp
    refine mul_nonneg (Finset.sum_nonneg fun i _ => ?_)
      (Real.log_nonneg (by exact_mod_cast (Nat.Prime.one_le (Nat.prime_of_mem_primesLE hp))))
    positivity
  have hmono : (∑ p ∈ ({2,3,5,7} : Finset ℕ),
        (∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ))
      ≤ (∑ p ∈ n.primesLE,
        (∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => hnonneg p hp)
  have hnn : ∀ p ∈ ({2,3,5,7} : Finset ℕ),
      0 ≤ (∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals
      refine mul_nonneg (Finset.sum_nonneg fun i _ => by positivity)
        (Real.log_nonneg (by norm_num))
  have t2 : ((∑ i ∈ Finset.Ico 2 (n + 1), ((n / 2 ^ i : ℕ) : ℝ)) * Real.log (2:ℝ))
      ≤ (∑ p ∈ ({2,3,5,7} : Finset ℕ),
        (∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ)) :=
    Finset.single_le_sum hnn (by simp)
  have t3 : ((∑ i ∈ Finset.Ico 2 (n + 1), ((n / 3 ^ i : ℕ) : ℝ)) * Real.log (3:ℝ))
      ≤ (∑ p ∈ ({2,3,5,7} : Finset ℕ),
        (∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ)) :=
    Finset.single_le_sum hnn (by simp)
  have t5 : ((∑ i ∈ Finset.Ico 2 (n + 1), ((n / 5 ^ i : ℕ) : ℝ)) * Real.log (5:ℝ))
      ≤ (∑ p ∈ ({2,3,5,7} : Finset ℕ),
        (∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ)) :=
    Finset.single_le_sum hnn (by simp)
  have t7 : ((∑ i ∈ Finset.Ico 2 (n + 1), ((n / 7 ^ i : ℕ) : ℝ)) * Real.log (7:ℝ))
      ≤ (∑ p ∈ ({2,3,5,7} : Finset ℕ),
        (∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ)) :=
    Finset.single_le_sum hnn (by simp)
  have e2 := inner_two_ge n hn
  have e3 := inner_three_ge n hn
  have e5 := inner_five_ge n hn
  have e7 := inner_seven_ge n hn
  have b2 : (0.484375 * (n:ℝ) - 5) * Real.log (2:ℝ)
      ≤ (∑ i ∈ Finset.Ico 2 (n + 1), ((n / 2 ^ i : ℕ) : ℝ)) * Real.log (2:ℝ) :=
    mul_le_mul_of_nonneg_right e2 (Real.log_nonneg (by norm_num))
  have b3 : (0.1604938271 * (n:ℝ) - 3) * Real.log (3:ℝ)
      ≤ (∑ i ∈ Finset.Ico 2 (n + 1), ((n / 3 ^ i : ℕ) : ℝ)) * Real.log (3:ℝ) :=
    mul_le_mul_of_nonneg_right e3 (Real.log_nonneg (by norm_num))
  have b5 : (0.04 * (n:ℝ) - 1) * Real.log (5:ℝ)
      ≤ (∑ i ∈ Finset.Ico 2 (n + 1), ((n / 5 ^ i : ℕ) : ℝ)) * Real.log (5:ℝ) :=
    mul_le_mul_of_nonneg_right e5 (Real.log_nonneg (by norm_num))
  have b7 : (0.0204081632 * (n:ℝ) - 1) * Real.log (7:ℝ)
      ≤ (∑ i ∈ Finset.Ico 2 (n + 1), ((n / 7 ^ i : ℕ) : ℝ)) * Real.log (7:ℝ) :=
    mul_le_mul_of_nonneg_right e7 (Real.log_nonneg (by norm_num))
  have key : 0.6159 * (n:ℝ) - 10.32 ≤ (0.484375 * (n:ℝ) - 5) * Real.log (2:ℝ)
      + (0.1604938271 * (n:ℝ) - 3) * Real.log (3:ℝ)
      + (0.04 * (n:ℝ) - 1) * Real.log (5:ℝ)
      + (0.0204081632 * (n:ℝ) - 1) * Real.log (7:ℝ) := by
    have h7 := log7_lb
    have h2 := log2_lb
    have h3 := log3_lb
    have h5 := log5_lb
    have hn100 : (100:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    nlinarith [h2, h3, h5, h7, hn100]
  have hsum4 : (∑ p ∈ ({2,3,5,7} : Finset ℕ),
        (∑ i ∈ Finset.Ico 2 (n + 1), ((n / p ^ i : ℕ) : ℝ)) * Real.log (p : ℝ))
      = ((∑ i ∈ Finset.Ico 2 (n + 1), ((n / 2 ^ i : ℕ) : ℝ)) * Real.log (2:ℝ))
        + ((∑ i ∈ Finset.Ico 2 (n + 1), ((n / 3 ^ i : ℕ) : ℝ)) * Real.log (3:ℝ))
        + ((∑ i ∈ Finset.Ico 2 (n + 1), ((n / 5 ^ i : ℕ) : ℝ)) * Real.log (5:ℝ))
        + ((∑ i ∈ Finset.Ico 2 (n + 1), ((n / 7 ^ i : ℕ) : ℝ)) * Real.log (7:ℝ)) := by
    rw [show ({2,3,5,7} : Finset ℕ) = insert 2 (insert 3 (insert 5 (insert 7 (∅ : Finset ℕ)))) from rfl]
    rw [Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_empty]
    all_goals simp
    ring
  linarith [hmono, hsum4, b2, b3, b5, b7, key]

private lemma log2_ub2 : Real.log 2 ≤ (0.6931471808 : ℝ) := le_of_lt Real.log_two_lt_d9
private lemma log5_ub : Real.log 5 ≤ (1.6094379126 : ℝ) := le_of_lt Real.log_five_lt_d9

private lemma log1000_le : Real.log (1000:ℝ) ≤ 6.9078 := by
  have he : Real.log (1000:ℝ) = 3 * Real.log 2 + 3 * Real.log 5 := by
    rw [show (1000:ℝ) = 2^3 * 5^3 by norm_num, Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]
    ring
  rw [he]
  linarith [log2_ub, log5_ub]

private lemma log_bound_aux (n : ℕ) (hn : 1000 ≤ n) :
    1 + Real.log (n:ℝ) + 10.32 ≤ 0.0209 * (n:ℝ) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by positivity
  have h1000 : (0:ℝ) < (1000:ℝ) := by norm_num
  have hlog : Real.log (n:ℝ) ≤ Real.log (1000:ℝ) + ((n:ℝ)/1000 - 1) := by
    have h1 : Real.log (n:ℝ) - Real.log (1000:ℝ) = Real.log ((n:ℝ)/1000) :=
      (Real.log_div (ne_of_gt hn0) (ne_of_gt h1000)).symm
    have h2 : Real.log ((n:ℝ)/1000) ≤ (n:ℝ)/1000 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    linarith
  have hnR : (1000:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  linarith [hlog, log1000_le]

private lemma logDiv_le_log_sub_83 (n : ℕ) (hn : 1000 ≤ n) :
    logDiv (n : ℝ) ≤ Real.log (n : ℝ) - 0.83 := by
  have hn2 : 2 ≤ n := by omega
  have hn0 : (0:ℝ) < (n:ℝ) := by positivity
  have hfac := (Commons.Analysis.SpecialFunctions.Log.log_factorial_sub_bounds hn2).2
  have hF := fracSum_le n hn
  have hT := tailSum_ge n (by omega)
  have haux := log_bound_aux n hn
  have hle : (n:ℝ) * logDiv (n:ℝ) ≤ (n:ℝ) * (Real.log (n:ℝ) - 0.83) := by
    have hld : logDiv (n:ℝ) = ∑ p ∈ n.primesLE, Real.log (p:ℝ)/(p:ℝ) := by
      unfold logDiv; rw [Nat.floor_natCast]
    rw [hld, legendre_sum_identity n]
    nlinarith [hfac, hF, hT, haux]
  exact (mul_le_mul_iff_of_pos_left hn0).mp hle

/-- Real version of the deficiency bound. -/
private lemma logDiv_le_log_sub_83_real (t : ℝ) (ht : 1000 ≤ t) :
    logDiv t ≤ Real.log t - 0.83 := by
  have hn : 1000 ≤ ⌊t⌋₊ := by
    have h := Nat.floor_mono ht
    simpa using h
  have h := logDiv_le_log_sub_83 ⌊t⌋₊ hn
  have hlog : Real.log ((⌊t⌋₊:ℕ):ℝ) ≤ Real.log t :=
    Real.log_le_log (by positivity) (Nat.floor_le (by linarith))
  have hld : logDiv t = logDiv ((⌊t⌋₊:ℕ):ℝ) := by
    unfold logDiv; rw [Nat.floor_natCast]
  linarith [h, hlog, hld]

/-! ## The logarithmic logarithm bounds at the block starts -/

private lemma loglog_bound (a : ℕ) (M lo L : ℝ) (ha : 2 ≤ a)
    (hM : M ≤ Real.log (a:ℝ)) (hlo : 0 < lo) (hloM : lo ≤ M)
    (hL : L ≤ Real.log lo + 2*(M/lo - 1)/((M/lo - 1) + 2)) :
    L ≤ Real.log (Real.log (a:ℝ)) := by
  have haR : (1:ℝ) < (a:ℝ) := by exact_mod_cast (by omega : 1 < a)
  have hlogapos : 0 < Real.log (a:ℝ) := Real.log_pos haR
  have hMpos : 0 < M := lt_of_lt_of_le hlo hloM
  have hx : 0 ≤ M/lo - 1 := by
    have h1 : (1:ℝ) ≤ M/lo := (one_le_div hlo).mpr hloM
    linarith
  have h1 : Real.log lo + 2*(M/lo - 1)/((M/lo - 1) + 2) ≤ Real.log lo + Real.log (M/lo) := by
    have h := Real.le_log_one_add_of_nonneg hx
    have h2 : Real.log (M/lo) = Real.log (1 + (M/lo - 1)) := by congr 1; ring
    linarith [h, h2]
  have h2 : Real.log lo + Real.log (M/lo) ≤ Real.log (Real.log (a:ℝ)) := by
    rw [← Real.log_mul (ne_of_gt hlo) (div_ne_zero (ne_of_gt hMpos) (ne_of_gt hlo))]
    apply Real.log_le_log
    · exact mul_pos hlo (div_pos hMpos hlo)
    · rw [mul_div_cancel₀ _ (ne_of_gt hlo)]
      exact hM
  linarith [hL, h1, h2]

private lemma loglog_100 : (1.5271795:ℝ) ≤ Real.log (Real.log (100:ℝ)) := by
  refine loglog_bound 100 (11512925463/2500000000) (9375/2048) (1.5271795) (by norm_num) ?_ (by norm_num) (by norm_num) ?_
  · rw [show ((100:ℕ):ℝ) = 2^2 * 5^2 by norm_num, Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]
    push_cast
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  · have hlo : (1.5211828:ℝ) ≤ Real.log (9375/2048) := by
      rw [show (9375/2048:ℝ) = 3 * 5^5 / 2^11 by norm_num,
          Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
          Real.log_pow, Real.log_pow]
      push_cast
      linarith [Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
    have hstep : (0.0059967:ℝ) ≤ 2*((11512925463:ℝ)/2500000000/(9375/2048) - 1)/(((11512925463:ℝ)/2500000000/(9375/2048) - 1) + 2) := by norm_num
    linarith

private lemma loglog_162 : (1.6268054:ℝ) ≤ Real.log (Real.log (162:ℝ)) := by
  refine loglog_bound 162 (50875963343/10000000000) (15625/3072) (1.6268054) (by norm_num) ?_ (by norm_num) (by norm_num) ?_
  · rw [show ((162:ℕ):ℝ) = 2^1 * 3^4 by norm_num, Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]
    push_cast
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]
  · have hlo : (1.6265433:ℝ) ≤ Real.log (15625/3072) := by
      rw [show (15625/3072:ℝ) = 5^6 / (3 * 2^10) by norm_num,
          Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
          Real.log_pow, Real.log_pow]
      push_cast
      linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_gt_d9]
    have hstep : (0.0002621:ℝ) ≤ 2*((50875963343:ℝ)/10000000000/(15625/3072) - 1)/(((50875963343:ℝ)/10000000000/(15625/3072) - 1) + 2) := by norm_num
    linarith

private lemma loglog_270 : (1.7224846:ℝ) ≤ Real.log (Real.log (270:ℝ)) := by
  refine loglog_bound 270 (55984219581/10000000000) (91125/16384) (1.7224846) (by norm_num) ?_ (by norm_num) (by norm_num) ?_
  · rw [show ((270:ℕ):ℝ) = 2^1 * 3^3 * 5^1 by norm_num, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
  · have hlo : (1.7159269:ℝ) ≤ Real.log (91125/16384) := by
      rw [show (91125/16384:ℝ) = 3^6 * 5^3 / 2^14 by norm_num,
          Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
          Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast
      linarith [Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
    have hstep : (0.0065577:ℝ) ≤ 2*((55984219581:ℝ)/10000000000/(91125/16384) - 1)/(((55984219581:ℝ)/10000000000/(91125/16384) - 1) + 2) := by norm_num
    linarith

private lemma loglog_500 : (1.8269025:ℝ) ≤ Real.log (Real.log (500:ℝ)) := by
  refine loglog_bound 500 (2485843239/400000000) (50625/8192) (1.8269025) (by norm_num) ?_ (by norm_num) (by norm_num) ?_
  · rw [show ((500:ℕ):ℝ) = 2^2 * 5^3 by norm_num, Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]
    push_cast
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  · have hlo : (1.8212874:ℝ) ≤ Real.log (50625/8192) := by
      rw [show (50625/8192:ℝ) = 3^4 * 5^4 / 2^13 by norm_num,
          Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
          Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast
      linarith [Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
    have hstep : (0.0056151:ℝ) ≤ 2*((2485843239:ℝ)/400000000/(50625/8192) - 1)/(((2485843239:ℝ)/400000000/(50625/8192) - 1) + 2) := by norm_num
    linarith

private lemma loglog_1000 : (1.9326446:ℝ) ≤ Real.log (Real.log (1000:ℝ)) := by
  refine loglog_bound 1000 (34538776389/5000000000) (28125/4096) (1.9326446) (by norm_num) ?_ (by norm_num) (by norm_num) ?_
  · rw [show ((1000:ℕ):ℝ) = 2^3 * 5^3 by norm_num, Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]
    push_cast
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  · have hlo : (1.9266479:ℝ) ≤ Real.log (28125/4096) := by
      rw [show (28125/4096:ℝ) = 3^2 * 5^5 / 2^12 by norm_num,
          Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
          Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast
      linarith [Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
    have hstep : (0.0059967:ℝ) ≤ 2*((34538776389/5000000000)/(28125/4096) - 1)/(((34538776389/5000000000)/(28125/4096) - 1) + 2) := by norm_num
    linarith

private lemma loglog_2250 : (2.0436439:ℝ) ≤ Real.log (Real.log (2250:ℝ)) := by
  refine loglog_bound 2250 (38593427471/5000000000) (625/81) (2.0436439) (by norm_num) ?_ (by norm_num) (by norm_num) ?_
  · rw [show ((2250:ℕ):ℝ) = 2^1 * 3^2 * 5^3 by norm_num, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
  · have hlo : (2.0433024:ℝ) ≤ Real.log (625/81) := by
      rw [show (625/81:ℝ) = 5^4 / 3^4 by norm_num,
          Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      push_cast
      linarith [Real.log_three_lt_d9, Real.log_five_gt_d9]
    have hstep : (0.0003415:ℝ) ≤ 2*((38593427471/5000000000)/(625/81) - 1)/(((38593427471/5000000000)/(625/81) - 1) + 2) := by norm_num
    linarith

private lemma loglog_5400 : (2.1510822:ℝ) ≤ Real.log (Real.log (5400:ℝ)) := by
  refine loglog_bound 5400 (8594154231/1000000000) (140625/16384) (2.1510822) (by norm_num) ?_ (by norm_num) (by norm_num) ?_
  · rw [show ((5400:ℕ):ℝ) = 2^3 * 3^3 * 5^2 by norm_num, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    linarith [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
  · have hlo : (2.1497915:ℝ) ≤ Real.log (140625/16384) := by
      rw [show (140625/16384:ℝ) = 3^2 * 5^6 / 2^14 by norm_num,
          Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
          Real.log_pow, Real.log_pow, Real.log_pow]
      push_cast
      linarith [Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
    have hstep : (0.0012907:ℝ) ≤ 2*((8594154231/1000000000)/(140625/16384) - 1)/(((8594154231/1000000000)/(140625/16384) - 1) + 2) := by norm_num
    linarith

private lemma logRatioSum_eq_primeRecips_add (x : ℝ) :
    logRatioSum x = primeRecips x + logRatioCorrSum x := by
  unfold logRatioSum primeRecips logRatioCorrSum corrTerm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  ring

private lemma corrSum_le_real (y : ℕ) : logRatioCorrSum (y:ℝ) ≤ 0.318 := by
  unfold logRatioCorrSum
  rw [Nat.floor_natCast]
  exact corr_sum_le y

private lemma intervalIntegrable_recip_log (a b : ℝ) (ha : 1000 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (t * Real.log t)⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro z hz
  rw [Set.uIcc_of_le hab] at hz
  have hz0 : z ≠ 0 := by linarith [hz.1]
  have hlogz : Real.log z ≠ 0 := by
    apply log_ne_zero_of_pos_of_ne_one <;> linarith [hz.1]
  exact ((continuousAt_id.mul (Real.continuousAt_log hz0)).inv₀
    (mul_ne_zero hz0 hlogz)).continuousWithinAt

private lemma intervalIntegrable_recip_log_sq (a b : ℝ) (ha : 1000 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (t * (Real.log t)^2)⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro z hz
  rw [Set.uIcc_of_le hab] at hz
  have hz0 : z ≠ 0 := by linarith [hz.1]
  have hlogz : Real.log z ≠ 0 := by
    apply log_ne_zero_of_pos_of_ne_one <;> linarith [hz.1]
  exact ((continuousAt_id.mul ((Real.continuousAt_log hz0).pow 2)).inv₀
    (mul_ne_zero hz0 (pow_ne_zero 2 hlogz))).continuousWithinAt

private lemma primeRecips_sub_loglog_le (y : ℝ) (hy : 10000 ≤ y) :
    primeRecips y - Real.log (Real.log y) ≤
      (primeRecips 10000 - Real.log (Real.log 10000)) + 0.93 / Real.log 10000 := by
  have h := primeRecips_loglog_diff (x := (10000:ℝ)) (X := y) (B₁ := 0) (by norm_num) hy
  simp only [sub_zero] at h
  have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog10 : 0 < Real.log (10000:ℝ) := Real.log_pos (by norm_num)
  have h1 : (logDiv y - Real.log y) / Real.log y ≤ -0.83 / Real.log y := by
    have hd := logDiv_le_log_sub_83_real y (by linarith)
    rw [div_le_div_iff_of_pos_right hlogy]
    linarith
  have h2 : -(1.76 / Real.log (10000:ℝ))
      ≤ (logDiv (10000:ℝ) - Real.log (10000:ℝ)) / Real.log (10000:ℝ) := by
    have hd := logDiv_ge_log_sub_sharp (10000:ℝ) (by norm_num)
    rw [le_div_iff₀ hlog10]
    have hcoe : -(1.76 / Real.log (10000:ℝ)) * Real.log (10000:ℝ) = -1.76 := by
      field_simp
    rw [hcoe]
    linarith
  have hB : IntervalIntegrable (fun t : ℝ => logDiv t / (t * (Real.log t)^2))
      volume (10000:ℝ) y := intervalIntegrable_logDiv_div_id_log_sq_gen (by norm_num) hy
  have hA : IntervalIntegrable (fun t : ℝ => (t * Real.log t)⁻¹) volume (10000:ℝ) y :=
    intervalIntegrable_recip_log (10000:ℝ) y (by norm_num) hy
  have hf : IntervalIntegrable
      (fun t : ℝ => (Real.log t - logDiv t) / (t * (Real.log t)^2)) volume (10000:ℝ) y :=
    IntervalIntegrable.congr (by
      intro t ht
      rw [Set.uIoc_of_le hy] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hlogt : Real.log t ≠ 0 := by
        apply log_ne_zero_of_pos_of_ne_one <;> linarith [ht.1]
      show (t * Real.log t)⁻¹ - logDiv t / (t * (Real.log t)^2)
          = (Real.log t - logDiv t) / (t * (Real.log t)^2)
      field_simp
      try ring) (hA.sub hB)
  have h3 : (∫ t in (10000:ℝ)..y, (logDiv t - Real.log t) / (t * (Real.log t)^2))
      ≤ -0.83 * (1/Real.log (10000:ℝ) - 1/Real.log y) := by
    have heq : (∫ t in (10000:ℝ)..y, (logDiv t - Real.log t) / (t * (Real.log t)^2))
        = -∫ t in (10000:ℝ)..y, (Real.log t - logDiv t) / (t * (Real.log t)^2) := by
      have hfun : (fun t : ℝ => (logDiv t - Real.log t) / (t * (Real.log t)^2))
          = (fun t : ℝ => -((Real.log t - logDiv t) / (t * (Real.log t)^2))) := by
        funext t; ring
      rw [hfun, intervalIntegral.integral_neg]
    rw [heq]
    have hpt : ∀ t ∈ Set.Icc (10000:ℝ) y,
        (0.83:ℝ) * ((t * (Real.log t)^2)⁻¹) ≤ (Real.log t - logDiv t) / (t * (Real.log t)^2) := by
      intro t ht
      have ht1 : 1000 ≤ t := by linarith [ht.1]
      have hd := logDiv_le_log_sub_83_real t ht1
      have ht0 : (0:ℝ) < t := by linarith [ht.1]
      have hlogt : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
      have hden : 0 < t * (Real.log t)^2 := by positivity
      rw [show (0.83:ℝ) * (t * (Real.log t)^2)⁻¹ = 0.83/(t * (Real.log t)^2) by rw [div_eq_mul_inv]]
      exact (div_le_div_iff_of_pos_right hden).mpr (by linarith [hd])
    have hg : IntervalIntegrable (fun t : ℝ => (0.83:ℝ) * ((t * (Real.log t)^2)⁻¹))
        volume (10000:ℝ) y :=
      (intervalIntegrable_recip_log_sq (10000:ℝ) y (by norm_num) hy).const_mul 0.83
    have hmono := intervalIntegral.integral_mono_on hy hg hf hpt
    have hval : (∫ t in (10000:ℝ)..y, (0.83:ℝ) * ((t * (Real.log t)^2)⁻¹))
        = 0.83 * ((Real.log (10000:ℝ))⁻¹ - (Real.log y)⁻¹) := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      rw [show (fun t : ℝ => (t * (Real.log t)^2)⁻¹) = (fun t : ℝ => t⁻¹ / (Real.log t)^2) from by
        funext t; rw [div_eq_mul_inv, mul_inv]]
      exact integral_inv_div_log_sq (by norm_num) (by linarith : (1:ℝ) < y)
    rw [hval] at hmono
    have : 0.83 * ((Real.log (10000:ℝ))⁻¹ - (Real.log y)⁻¹)
        = 0.83 * (1/Real.log (10000:ℝ) - 1/Real.log y) := by ring
    linarith [hmono, this.le]
  have hsum : (primeRecips y - Real.log (Real.log y)) - (primeRecips 10000 - Real.log (Real.log 10000))
      ≤ -0.83 / Real.log y + (1.76 / Real.log (10000:ℝ))
        + (-0.83 * (1/Real.log (10000:ℝ) - 1/Real.log y)) := by
    linarith [h, h1, h2, h3]
  have hrew : -0.83 / Real.log y + (1.76 / Real.log (10000:ℝ))
      + (-0.83 * (1/Real.log (10000:ℝ) - 1/Real.log y)) = 0.93 / Real.log (10000:ℝ) := by
    field_simp
    ring
  linarith [hsum, hrew.le]


private lemma loglog_10000 : (2.2203267:ℝ) ≤ Real.log (Real.log (10000:ℝ)) := by
  refine loglog_bound 10000 (11512925463/1250000000) (9375/1024) (2.2203267) (by norm_num) ?_ (by norm_num) (by norm_num) ?_
  · rw [show ((10000:ℕ):ℝ) = 2^4 * 5^4 by norm_num, Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]
    push_cast
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  · have hlo : (2.2143300:ℝ) ≤ Real.log (9375/1024) := by
      rw [show (9375/1024:ℝ) = 3 * 5^5 / 2^10 by norm_num,
          Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
          Real.log_pow, Real.log_pow]
      push_cast
      linarith [Real.log_two_lt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
    have hstep : (0.0059967:ℝ) ≤ 2*((11512925463:ℝ)/1250000000/(9375/1024) - 1)/(((11512925463:ℝ)/1250000000/(9375/1024) - 1) + 2) := by norm_num
    linarith

/-- The reciprocal sum is at most the ceiling sum divided by `2 ^ 40`. -/
private lemma sum_inv_le_ceil (s : Finset ℕ) (h0 : ∀ n ∈ s, 0 < n) :
    (∑ n ∈ s, (1:ℝ)/n) ≤ (∑ n ∈ s, ((2^40 + n - 1)/n : ℕ)) / 2^40 := by
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro n hn
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast h0 n hn
  have hnat : 2^40 ≤ n * ((2^40 + n - 1)/n) := by
    have h1 : n * ((2^40 + n - 1)/n) + (2^40 + n - 1) % n = 2^40 + n - 1 := Nat.div_add_mod _ _
    have h2 : (2^40 + n - 1) % n < n := Nat.mod_lt _ (h0 n hn)
    omega
  have hreal : (2:ℝ)^40 ≤ (n:ℝ) * (((2^40 + n - 1)/n : ℕ) : ℝ) := by
    have h3 : ((2^40:ℕ):ℝ) ≤ ((n * ((2^40 + n - 1)/n) : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at h3
    linarith
  have hgoal : (1:ℝ) * (2:ℝ)^40 ≤ (((2^40 + n - 1)/n : ℕ) : ℝ) * (n:ℝ) := by linarith
  exact (div_le_div_iff₀ hn0 (by norm_num : (0:ℝ) < (2:ℝ)^40)).mpr hgoal

private abbrev copList : List ℕ :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]

private abbrev cop100 (n : ℕ) : Prop := ∀ q ∈ copList, ¬ q ∣ n

private def sieveCum (b : ℕ) : ℕ :=
  ∑ n ∈ (Finset.Icc 101 b).filter cop100, (2^40 + n - 1)/n

private lemma copList_prime : ∀ q ∈ copList, Nat.Prime q := by decide

private lemma primesLE100_eq : Nat.primesLE 100 = copList.toFinset := by decide

private lemma sieveCum_162 : sieveCum 162 ≤ 106305031285 := by decide
private lemma sieveCum_276 : sieveCum 276 ≤ 215419443051 := by decide
private lemma sieveCum_502 : sieveCum 502 ≤ 323138058143 := by decide
private lemma sieveCum_1020 : sieveCum 1020 ≤ 437850299504 := by decide
private lemma sieveCum_2250 : sieveCum 2250 ≤ 554453621604 := by decide
private lemma sieveCum_5622 : sieveCum 5622 ≤ 676630464597 := by decide
private lemma sieveCum_10000 : sieveCum 10000 ≤ 747934809752 := by decide

private lemma primeRecips100_ceil :
    (∑ p ∈ Nat.primesLE 100, ((2^40 + p - 1)/p : ℕ)) ≤ 1982218475324 := by decide

private lemma primeSum_le_sieve (b : ℕ) (hb : b ≤ 10000) :
    (∑ p ∈ (Nat.primesLE b).filter (fun p => 100 < p), (1:ℝ)/p) ≤ (sieveCum b : ℝ)/2^40 := by
  have hsub : (Nat.primesLE b).filter (fun p => 100 < p)
      ⊆ (Finset.Icc 101 b).filter cop100 := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    obtain ⟨hp1, hp2⟩ := hp
    have hpP : p.Prime := (Nat.mem_primesLE.mp hp1).2
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, (Nat.mem_primesLE.mp hp1).1⟩, ?_⟩
    intro q hq hqdiv
    have hqP : q.Prime := copList_prime q hq
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hqP hpP).mp hqdiv
    have hqle : q ≤ 97 := by
      simp only [copList, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> omega
    omega
  calc (∑ p ∈ (Nat.primesLE b).filter (fun p => 100 < p), (1:ℝ)/p)
      ≤ ∑ n ∈ (Finset.Icc 101 b).filter cop100, (1:ℝ)/n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => by positivity)
    _ ≤ (∑ n ∈ (Finset.Icc 101 b).filter cop100, ((2^40 + n - 1)/n : ℕ))/2^40 :=
        sum_inv_le_ceil _ (fun n hn => by
          rw [Finset.mem_filter, Finset.mem_Icc] at hn
          omega)
    _ = (sieveCum b : ℝ)/2^40 := by
        unfold sieveCum
        push_cast
        ring


private lemma one_sub_inv_pos' {p : ℕ} (hp : 2 ≤ p) : (0:ℝ) < 1 - (p:ℝ)⁻¹ := by
  have hp2' : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have h1 : (1:ℝ)/2 ≤ 1 - (p:ℝ)⁻¹ := by
    have := one_div_le_one_div_of_le (show (0:ℝ) < 2 by norm_num) hp2'
    rw [one_div] at this ⊢; linarith
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) h1

private lemma prodLog_eq' (n : ℕ) (h : ∀ p ∈ Nat.primesLE n, (1:ℝ) < (p:ℝ)) :
    Real.log (∏ p ∈ Nat.primesLE n, (1 - (p:ℝ)⁻¹)) = -logRatioSum (n:ℝ) := by
  rw [Real.log_prod (fun p hp => by
    have hlt : 1 < p := by exact_mod_cast (h p hp)
    exact ne_of_gt (one_sub_inv_pos' (by omega : 2 ≤ p)))]
  have hsum : logRatioSum (n:ℝ) = ∑ p ∈ (Nat.primesLE n), Real.log ((p:ℝ)/((p:ℝ)-1)) := by
    unfold logRatioSum; rw [Nat.floor_natCast]
  rw [hsum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp1 := h p hp
  have hp0 : (0:ℝ) < (p:ℝ) := by linarith
  have hp1' : (0:ℝ) < (p:ℝ) - 1 := by linarith
  have : 1 - (p:ℝ)⁻¹ = (((p:ℝ)/((p:ℝ)-1))⁻¹) := by field_simp
  rw [this, Real.log_inv]

private lemma primeRecips100_le : primeRecips (100:ℝ) ≤ (1982218475324:ℝ)/2^40 := by
  unfold primeRecips
  rw [show ⌊(100:ℝ)⌋₊ = 100 from by norm_num]
  calc (∑ p ∈ Nat.primesLE 100, (1:ℝ)/p)
      ≤ (∑ p ∈ Nat.primesLE 100, ((2^40 + p - 1)/p : ℕ))/2^40 :=
        sum_inv_le_ceil _ (fun n hn => (Nat.mem_primesLE.mp hn).2.pos)
    _ ≤ (1982218475324:ℝ)/2^40 := by
        have hR : ((∑ p ∈ Nat.primesLE 100, ((2^40 + p - 1)/p : ℕ)) : ℝ) ≤ 1982218475324 := by
          exact_mod_cast primeRecips100_ceil
        push_cast at hR
        rw [div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2^40)]
        push_cast
        linarith

private lemma primes100_10000_sub : Nat.primesLE 100 ⊆ Nat.primesLE 10000 := by
  intro p hp
  rw [Nat.mem_primesLE] at hp ⊢
  exact ⟨by omega, hp.2⟩

private lemma primes_100_10000_diff : Nat.primesLE 10000 \ Nat.primesLE 100
    = (Nat.primesLE 10000).filter (fun p => 100 < p) := by
  ext p
  simp only [Finset.mem_sdiff, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨h1,h2⟩, h3⟩
    exact ⟨⟨h1,h2⟩, not_le.mp (fun hc => h3 ⟨hc,h2⟩)⟩
  · rintro ⟨⟨h1,h2⟩, h3⟩
    exact ⟨⟨h1,h2⟩, fun hc => absurd h3 (not_lt.mpr hc.1)⟩

private lemma primeRecips10000_le :
    primeRecips (10000:ℝ) ≤ ((1982218475324 + 747934809752 : ℕ):ℝ)/2^40 := by
  have hX : (∑ p ∈ (Nat.primesLE 10000).filter (fun p => 100 < p), (1:ℝ)/p)
      ≤ (747934809752:ℝ)/2^40 := by
    refine le_trans ?_ (primeSum_le_sieve 10000 (by norm_num))
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨Nat.mem_primesLE.mpr (Nat.mem_primesLE.mp hp.1), hp.2⟩
    · intro p _ _; positivity
  have hsplit : primeRecips (10000:ℝ) = primeRecips (100:ℝ)
      + ∑ p ∈ (Nat.primesLE 10000).filter (fun p => 100 < p), (1:ℝ)/p := by
    unfold primeRecips
    rw [show ⌊(10000:ℝ)⌋₊ = 10000 from by norm_num, show ⌊(100:ℝ)⌋₊ = 100 from by norm_num]
    rw [← primes_100_10000_diff]
    rw [← Finset.sum_sdiff (f := fun p : ℕ => (1:ℝ)/p) primes100_10000_sub]
    ring
  have hA := primeRecips100_le
  rw [hsplit]
  push_cast
  linarith

private lemma small_y (y : ℕ) (h100 : 100 ≤ y) (hY : y ≤ 10000) :
    logRatioSum (y:ℝ) ≤ Real.log (Real.log (y:ℝ)) + 0.6931471803 := by
  have hcorr : logRatioCorrSum (y:ℝ) ≤ 0.318 := corrSum_le_real y
  have hdecomp := logRatioSum_eq_primeRecips_add (y:ℝ)
  have hsub100 : Nat.primesLE 100 ⊆ Nat.primesLE y := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨le_trans hp.1 h100, hp.2⟩
  have hsdiff : Nat.primesLE y \ Nat.primesLE 100
      = (Nat.primesLE y).filter (fun p => 100 < p) := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨h1,h2⟩, h3⟩
      exact ⟨⟨h1,h2⟩, not_le.mp (fun hc => h3 ⟨hc,h2⟩)⟩
    · rintro ⟨⟨h1,h2⟩, h3⟩
      exact ⟨⟨h1,h2⟩, fun hc => absurd h3 (not_lt.mpr hc.1)⟩
  have hsplit : primeRecips (y:ℝ) = primeRecips (100:ℝ)
      + ∑ p ∈ (Nat.primesLE y).filter (fun p => 100 < p), (1:ℝ)/p := by
    unfold primeRecips
    rw [Nat.floor_natCast, show ⌊(100:ℝ)⌋₊ = 100 from by norm_num]
    rw [← hsdiff]
    rw [← Finset.sum_sdiff (f := fun p : ℕ => (1:ℝ)/p) hsub100]
    ring
  have hmono : ∀ b : ℕ, y ≤ b → b ≤ 10000 →
      (∑ p ∈ (Nat.primesLE y).filter (fun p => 100 < p), (1:ℝ)/p)
      ≤ (sieveCum b : ℝ)/2^40 := by
    intro b hyb hb
    refine le_trans ?_ (primeSum_le_sieve b hb)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨Nat.mem_primesLE.mpr ⟨le_trans (Nat.mem_primesLE.mp hp.1).1 hyb,
        (Nat.mem_primesLE.mp hp.1).2⟩, hp.2⟩
    · intro p _ _; positivity
  have hloglog_mono : ∀ a : ℕ, 100 ≤ a → a ≤ y →
      Real.log (Real.log (a:ℝ)) ≤ Real.log (Real.log (y:ℝ)) := by
    intro a ha hay
    have ha2 : 1 < a := lt_of_lt_of_le (by norm_num : 1 < 100) ha
    have h1 : (1:ℝ) < (a:ℝ) := by exact_mod_cast ha2
    have h2 : Real.log (a:ℝ) ≤ Real.log (y:ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hay)
    exact Real.log_le_log (Real.log_pos h1) h2
  have key : ∀ (b : ℕ) (L : ℝ), y ≤ b → b ≤ 10000 → L ≤ Real.log (Real.log (y:ℝ)) →
      (1982218475324:ℝ)/2^40 + (sieveCum b : ℝ)/2^40 + 0.318 ≤ L + 0.6931471803 →
      logRatioSum (y:ℝ) ≤ Real.log (Real.log (y:ℝ)) + 0.6931471803 := by
    intro b L hyb hb hL hcond
    have hX := hmono b hyb hb
    rw [hdecomp, hsplit]
    linarith [hcorr, hX, hL, hcond, primeRecips100_le]
  by_cases h1 : y ≤ 162
  · refine key 162 (1.5271795) h1 (by norm_num) (loglog_100.trans (hloglog_mono 100 (by norm_num) h100)) ?_
    · have hc : (sieveCum 162 : ℝ) ≤ 106305031285 := by exact_mod_cast sieveCum_162
      have hcond : (1982218475324:ℝ)/2^40 + (106305031285:ℝ)/2^40 + 0.318
          ≤ 1.5271795 + 0.6931471803 := by norm_num
      linarith
  · by_cases h2 : y ≤ 276
    · refine key 276 (1.6268054) h2 (by norm_num) (loglog_162.trans (hloglog_mono 162 (by norm_num) (le_of_lt (Nat.lt_of_not_le h1)))) ?_
      · have hc : (sieveCum 276 : ℝ) ≤ 215419443051 := by exact_mod_cast sieveCum_276
        have hcond : (1982218475324:ℝ)/2^40 + (215419443051:ℝ)/2^40 + 0.318
            ≤ 1.6268054 + 0.6931471803 := by norm_num
        linarith
    · by_cases h3 : y ≤ 502
      · refine key 502 (1.7224846) h3 (by norm_num) (loglog_270.trans (hloglog_mono 270 (by norm_num) (le_trans (by norm_num : (270:ℕ) ≤ 277) (Nat.succ_le_of_lt (Nat.lt_of_not_le h2))))) ?_
        · have hc : (sieveCum 502 : ℝ) ≤ 323138058143 := by exact_mod_cast sieveCum_502
          have hcond : (1982218475324:ℝ)/2^40 + (323138058143:ℝ)/2^40 + 0.318
              ≤ 1.7224846 + 0.6931471803 := by norm_num
          linarith
      · by_cases h4 : y ≤ 1020
        · refine key 1020 (1.8269025) h4 (by norm_num) (loglog_500.trans (hloglog_mono 500 (by norm_num) (le_trans (by norm_num : (500:ℕ) ≤ 503) (Nat.succ_le_of_lt (Nat.lt_of_not_le h3))))) ?_
          · have hc : (sieveCum 1020 : ℝ) ≤ 437850299504 := by exact_mod_cast sieveCum_1020
            have hcond : (1982218475324:ℝ)/2^40 + (437850299504:ℝ)/2^40 + 0.318
                ≤ 1.8269025 + 0.6931471803 := by norm_num
            linarith
        · by_cases h5 : y ≤ 2250
          · refine key 2250 (1.9326446) h5 (by norm_num) (loglog_1000.trans (hloglog_mono 1000 (by norm_num) (le_trans (by norm_num : (1000:ℕ) ≤ 1021) (Nat.succ_le_of_lt (Nat.lt_of_not_le h4))))) ?_
            · have hc : (sieveCum 2250 : ℝ) ≤ 554453621604 := by exact_mod_cast sieveCum_2250
              have hcond : (1982218475324:ℝ)/2^40 + (554453621604:ℝ)/2^40 + 0.318
                  ≤ 1.9326446 + 0.6931471803 := by norm_num
              linarith
          · by_cases h6 : y ≤ 5622
            · refine key 5622 (2.0436439) h6 (by norm_num) (loglog_2250.trans (hloglog_mono 2250 (by norm_num) (le_trans (by norm_num : (2250:ℕ) ≤ 2251) (Nat.succ_le_of_lt (Nat.lt_of_not_le h5))))) ?_
              · have hc : (sieveCum 5622 : ℝ) ≤ 676630464597 := by exact_mod_cast sieveCum_5622
                have hcond : (1982218475324:ℝ)/2^40 + (676630464597:ℝ)/2^40 + 0.318
                    ≤ 2.0436439 + 0.6931471803 := by norm_num
                linarith
            · refine key 10000 (2.1510822) hY (by norm_num) (loglog_5400.trans (hloglog_mono 5400 (by norm_num) (le_trans (by norm_num : (5400:ℕ) ≤ 5623) (Nat.succ_le_of_lt (Nat.lt_of_not_le h6))))) ?_
              · have hc : (sieveCum 10000 : ℝ) ≤ 747934809752 := by exact_mod_cast sieveCum_10000
                have hcond : (1982218475324:ℝ)/2^40 + (747934809752:ℝ)/2^40 + 0.318
                    ≤ 2.1510822 + 0.6931471803 := by norm_num
                linarith

private lemma logRatioSum_le_of_large (y : ℕ) (hY : 10000 ≤ y) :
    logRatioSum (y:ℝ) ≤ Real.log (Real.log (y:ℝ)) + 0.6931471803 := by
  have hy10 : (10000:ℝ) ≤ (y:ℝ) := by exact_mod_cast hY
  have h1 := primeRecips_sub_loglog_le (y:ℝ) hy10
  have h2 := logRatioSum_eq_primeRecips_add (y:ℝ)
  have h3 : logRatioCorrSum (y:ℝ) ≤ 0.318 := corrSum_le_real y
  have hlgl : (2.2203267:ℝ) ≤ Real.log (Real.log (10000:ℝ)) := loglog_10000
  have hlog10000 : (9.2103403:ℝ) ≤ Real.log (10000:ℝ) := by
    rw [show (10000:ℝ) = 2^4 * 5^4 by norm_num, Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]
    push_cast
    linarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have h9 : (0.93:ℝ)/Real.log (10000:ℝ) ≤ 0.100975 := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.log (10000:ℝ))]
    have hmul : (0.100975:ℝ) * 9.2103403 ≤ 0.100975 * Real.log (10000:ℝ) :=
      mul_le_mul_of_nonneg_left hlog10000 (by norm_num)
    linarith [hmul]
  have hprR : primeRecips (10000:ℝ) ≤ 2.4830600 := by
    have h := primeRecips10000_le
    have h2' : ((1982218475324 + 747934809752 : ℕ):ℝ)/2^40 ≤ 2.48306 := by norm_num
    linarith
  rw [h2]
  linarith [h1, h3, hprR, hlgl, h9]

theorem prodPrime_oneSubInv_ge_half (y : ℕ) (hy : 100 ≤ y) :
    (1 / 2 : ℝ) / Real.log (y : ℝ) ≤ ∏ p ∈ Nat.primesLE y, (1 - (p : ℝ)⁻¹) := by
  have hyR : (1:ℝ) < (y:ℝ) := by exact_mod_cast (by omega : 1 < y)
  have hlogy : 0 < Real.log (y:ℝ) := Real.log_pos hyR
  have hPpos : (0:ℝ) < ∏ p ∈ Nat.primesLE y, (1 - (p:ℝ)⁻¹) :=
    Finset.prod_pos (fun p hp => one_sub_inv_pos' (Nat.Prime.two_le (Nat.mem_primesLE.mp hp).2))
  have hlogP : Real.log (∏ p ∈ Nat.primesLE y, (1 - (p:ℝ)⁻¹)) = -logRatioSum (y:ℝ) :=
    prodLog_eq' y (fun p hp => by
      have hlt : 1 < p := (Nat.Prime.one_lt (Nat.mem_primesLE.mp hp).2)
      exact_mod_cast hlt)
  have hmain : logRatioSum (y:ℝ) ≤ Real.log (Real.log (y:ℝ)) + 0.6931471803 := by
    by_cases h : y ≤ 10000
    · exact small_y y hy h
    · exact logRatioSum_le_of_large y (by omega)
  have hlog2 : (0.6931471803:ℝ) ≤ Real.log 2 := le_of_lt Real.log_two_gt_d9
  have hexp : Real.exp (-Real.log (Real.log (y:ℝ)) - Real.log 2) = (1/2:ℝ)/Real.log (y:ℝ) := by
    rw [show -Real.log (Real.log (y:ℝ)) - Real.log 2
        = (-Real.log 2) + (-Real.log (Real.log (y:ℝ))) by ring, Real.exp_add,
        Real.exp_neg, Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2), Real.exp_log hlogy]
    ring
  rw [← hexp, ← Real.exp_log hPpos]
  apply Real.exp_le_exp.mpr
  rw [hlogP]
  linarith [hmain, hlog2]

end

end Commons.NumberTheory.Mertens
