import Mathlib
import Submission.Work.LinnikAreas.Density4.mu_kappa_log_sum

namespace Work.LinnikAreas.JutilaPieces

open Finset
open Work.LinnikAreas.Density4 (prodKappa sHalf prodKappa_mul_sHalf_le prodKappa_mul_sHalf_le_sq
  sHalf_nonneg divisors_sqrtrecip_mul_coprime tau_rpow_sum_bound)

noncomputable section

lemma prodKappa_nonneg' (d : ℕ) : 0 ≤ prodKappa d := by
  rw [Work.LinnikAreas.Density4.prodKappa]
  exact Finset.prod_nonneg (fun p hp => by positivity)

/-- `log (2+Q) ≤ 2 log Q` for `Q ≥ 2`. -/
lemma log_add_two_le_two_mul_log' (Q : ℝ) (hQ : 2 ≤ Q) :
    Real.log (2 + Q) ≤ 2 * Real.log Q := by
  have h : 2 + Q ≤ Q^2 := by nlinarith
  calc Real.log (2 + Q) ≤ Real.log (Q^2) := Real.log_le_log (by linarith) h
    _ = 2 * Real.log Q := by rw [Real.log_pow]; norm_num

/-- For `1 ≤ d` with `d² ≤ Q` and `Q ≥ 2`: `(log (2+Q/d))^{-A} ≤ 4^A (log (2+Q))^{-A}`. -/
lemma log_div_rpow_le_small {A Q : ℝ} (hA : 0 < A) (hQ : 2 ≤ Q) {d : ℕ} (hd : 1 ≤ d)
    (hdd : (d:ℝ) * (d:ℝ) ≤ Q) :
    (Real.log (2 + Q / (d:ℝ)))^(-A) ≤ 4^A * (Real.log (2 + Q))^(-A) := by
  have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hQpos : 0 < Q := by linarith
  have hqp : 0 < Q / (d:ℝ) := by positivity
  have hL1 : 0 < Real.log (2 + Q/(d:ℝ)) := Real.log_pos (by linarith)
  have hL2 : 0 < Real.log (2 + Q) := Real.log_pos (by linarith)
  have hdle : (d:ℝ) ≤ Real.sqrt Q := by
    rw [Real.le_sqrt hdpos.le hQpos.le]
    have h : (d:ℝ)^2 = (d:ℝ)*(d:ℝ) := by ring
    linarith
  have hqd : Real.sqrt Q ≤ Q/(d:ℝ) := by
    rw [le_div_iff₀ hdpos]
    have hsq : Real.sqrt Q * Real.sqrt Q = Q := by rw [← pow_two, Real.sq_sqrt hQpos.le]
    nlinarith [hsq, Real.sqrt_nonneg Q, hdle]
  have hlogb : (1/4) * Real.log (2 + Q) ≤ Real.log (2 + Q/(d:ℝ)) := by
    have h6 : Real.log (Real.sqrt Q) ≤ Real.log (2 + Q/(d:ℝ)) :=
      Real.log_le_log (Real.sqrt_pos.mpr hQpos) (by linarith)
    have h7 : Real.log (Real.sqrt Q) = Real.log Q / 2 := Real.log_sqrt hQpos.le
    rw [h7] at h6
    have h8 : Real.log (2+Q) ≤ 2*Real.log Q := log_add_two_le_two_mul_log' Q hQ
    linarith
  have h1 : (Real.log (2+Q))^A ≤ (4*Real.log (2 + Q/(d:ℝ)))^A :=
    Real.rpow_le_rpow hL2.le (by linarith) hA.le
  have h2 : (4*Real.log (2 + Q/(d:ℝ)))^(-A) ≤ (Real.log (2+Q))^(-A) := by
    have h := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hL2 A) h1
    rw [one_div, one_div, ← Real.rpow_neg (le_of_lt (by positivity : (0:ℝ) < 4*Real.log (2 + Q/(d:ℝ)))),
      ← Real.rpow_neg hL2.le] at h
    exact h
  have h3 : (Real.log (2 + Q/(d:ℝ)))^(-A) = 4^A * ((4*Real.log (2 + Q/(d:ℝ)))^(-A)) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hL1.le,
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4)]
    rw [← mul_assoc, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4),
      ← Real.rpow_add (by norm_num : (0:ℝ) < 4)]
    rw [show A + -A = 0 by ring, Real.rpow_zero, one_mul]
  calc (Real.log (2 + Q/(d:ℝ)))^(-A)
      = 4^A * ((4*Real.log (2 + Q/(d:ℝ)))^(-A)) := h3
    _ ≤ 4^A * ((Real.log (2+Q))^(-A)) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (by norm_num) A)

/-- For `1 ≤ d` and `Q ≥ 1`: `(log (2+Q/d))^{-A} ≤ (log 2)^{-A}`. -/
lemma log_div_rpow_le_big {A Q : ℝ} (hA : 0 < A) (hQ : 1 ≤ Q) {d : ℕ} (hd : 1 ≤ d) :
    (Real.log (2 + Q / (d:ℝ)))^(-A) ≤ (Real.log 2)^(-A) := by
  have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hqp : 0 < Q / (d:ℝ) := by positivity
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL1 : 0 < Real.log (2 + Q/(d:ℝ)) := Real.log_pos (by linarith)
  have h1 : Real.log 2 ≤ Real.log (2 + Q/(d:ℝ)) := Real.log_le_log (by norm_num) (by linarith)
  have h3 : (Real.log 2)^(-A) = ((Real.log 2)^A)⁻¹ := Real.rpow_neg hlog2pos.le A
  rw [Real.rpow_neg hL1.le A, h3]
  simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hlog2pos A)
    (Real.rpow_le_rpow hlog2pos.le h1 hA.le)

/-- The `1/√√Q` decay produced by the logarithm. -/
lemma inv_sqrt_sqrt_le_logpow (A : ℝ) (hA : 0 < A) (Q : ℝ) (hQ : 1 ≤ Q) :
    (Real.sqrt (Real.sqrt Q))⁻¹
      ≤ Real.sqrt (Real.sqrt 3) * (4*A)^A * (Real.log (2+Q))^(-A) := by
  have hAp : 0 < 4*A := by linarith
  have hQpos : 0 < Q := by linarith
  have h2Q : 0 < 2 + Q := by linarith
  have hlog : 0 < Real.log (2+Q) := Real.log_pos (by linarith)
  have hsqrt3pos : 0 < Real.sqrt (Real.sqrt 3) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
  have h1 : Real.log (2+Q) ≤ (2+Q)^(1/(4*A)) / (1/(4*A)) :=
    Commons.Analysis.ExpLog.log_le_rpow_div (by linarith) (by positivity)
  have h2 : (2+Q)^(1/(4*A)) / (1/(4*A)) = 4*A * (2+Q)^(1/(4*A)) := by
    rw [div_eq_mul_inv, one_div, inv_inv]; ring
  rw [h2] at h1
  have h3 : (Real.log (2+Q))^A ≤ (4*A * (2+Q)^(1/(4*A)))^A :=
    Real.rpow_le_rpow hlog.le h1 hA.le
  have h4 : (4*A * (2+Q)^(1/(4*A)))^A = (4*A)^A * Real.sqrt (Real.sqrt (2+Q)) := by
    rw [Real.mul_rpow hAp.le (Real.rpow_nonneg h2Q.le _), ← Real.rpow_mul h2Q.le]
    rw [show (1/(4*A)) * A = 1/4 by
      have h4A : (4*A) ≠ 0 := ne_of_gt hAp
      field_simp]
    rw [show (2+Q)^(1/4:ℝ) = Real.sqrt (Real.sqrt (2+Q)) by
      rw [show (1/4:ℝ) = (1/2)*(1/2) by norm_num, Real.rpow_mul h2Q.le,
        Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]]
  rw [h4] at h3
  have h5 : Real.sqrt (Real.sqrt (2+Q)) ≤ Real.sqrt (Real.sqrt 3) * Real.sqrt (Real.sqrt Q) := by
    have h6 : (2+Q) ≤ 3*Q := by linarith
    have h7 : Real.sqrt (Real.sqrt (2+Q)) ≤ Real.sqrt (Real.sqrt (3*Q)) :=
      Real.sqrt_le_sqrt (Real.sqrt_le_sqrt h6)
    have h8 : Real.sqrt (Real.sqrt (3*Q)) = Real.sqrt (Real.sqrt 3) * Real.sqrt (Real.sqrt Q) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3) Q]
      rw [Real.sqrt_mul (Real.sqrt_nonneg 3) (Real.sqrt Q)]
    linarith
  have h3' : (Real.log (2+Q))^A
      ≤ (4*A)^A * (Real.sqrt (Real.sqrt 3) * Real.sqrt (Real.sqrt Q)) :=
    le_trans h3 (mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hAp.le A))
  have h10 : ((4*A)^A * (Real.sqrt (Real.sqrt 3) * Real.sqrt (Real.sqrt Q)))⁻¹
      ≤ ((Real.log (2+Q))^A)⁻¹ := by
    have h := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hlog A) h3'
    rw [one_div, one_div] at h
    exact h
  have h11 : ((4*A)^A * (Real.sqrt (Real.sqrt 3) * Real.sqrt (Real.sqrt Q)))⁻¹
      = (4*A)^(-A) * (Real.sqrt (Real.sqrt 3))⁻¹ * (Real.sqrt (Real.sqrt Q))⁻¹ := by
    rw [mul_inv, mul_inv, Real.rpow_neg hAp.le]
    ring
  have h12 : (Real.sqrt (Real.sqrt Q))⁻¹
      ≤ (4*A)^A * Real.sqrt (Real.sqrt 3) * ((Real.log (2+Q))^A)⁻¹ := by
    have h13 := mul_le_mul_of_nonneg_left h10
      (mul_nonneg (Real.rpow_nonneg hAp.le A) (le_of_lt hsqrt3pos))
    rw [h11] at h13
    have h14 : (4*A)^A * Real.sqrt (Real.sqrt 3)
        * ((4*A)^(-A) * (Real.sqrt (Real.sqrt 3))⁻¹ * (Real.sqrt (Real.sqrt Q))⁻¹)
        = (Real.sqrt (Real.sqrt Q))⁻¹ := by
      have h15 : (4*A)^A * (4*A)^(-A) = 1 := by
        rw [← Real.rpow_add hAp]
        rw [show A + -A = 0 by ring, Real.rpow_zero]
      have h16 : Real.sqrt (Real.sqrt 3) * (Real.sqrt (Real.sqrt 3))⁻¹ = 1 :=
        mul_inv_cancel₀ (ne_of_gt hsqrt3pos)
      rw [show (4*A)^A * Real.sqrt (Real.sqrt 3)
          * ((4*A)^(-A) * (Real.sqrt (Real.sqrt 3))⁻¹ * (Real.sqrt (Real.sqrt Q))⁻¹)
          = ((4*A)^A * (4*A)^(-A)) * (Real.sqrt (Real.sqrt 3) * (Real.sqrt (Real.sqrt 3))⁻¹)
              * (Real.sqrt (Real.sqrt Q))⁻¹ from by ring]
      rw [h15, h16, one_mul, one_mul]
    rw [h14] at h13
    exact h13
  calc (Real.sqrt (Real.sqrt Q))⁻¹
      ≤ (4*A)^A * Real.sqrt (Real.sqrt 3) * ((Real.log (2+Q))^A)⁻¹ := h12
    _ = Real.sqrt (Real.sqrt 3) * (4*A)^A * (Real.log (2+Q))^(-A) := by
        rw [Real.rpow_neg hlog.le]; ring

/-- The weighted `Θ`-error sum bound, real `Q`, arbitrary exponent `A > 0`. -/
theorem kappaErrPowSelf (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ) (t : ℕ), 1 ≤ Q → 1 ≤ t →
      (∑ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Squarefree d ∧ Nat.Coprime d t),
          prodKappa d * sHalf (d * t) * (Real.log (2 + Q / (d:ℝ)))^(-A))
        ≤ C * sHalf t * (Real.log (2 + Q))^(-A) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hAp : 0 < 4*A := by linarith
  have hsqrt3pos : 0 < Real.sqrt (Real.sqrt 3) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
  set C : ℝ := 16 * (4:ℝ)^A + 16 * Real.sqrt (Real.sqrt 3) * (4*A)^A * (Real.log 2)^(-A) + 1
    with hCdef
  have hCnn : (0:ℝ) ≤ C - 1 := by
    rw [hCdef]
    have h1 : (0:ℝ) ≤ (4:ℝ)^A := Real.rpow_nonneg (by norm_num) A
    have h2 : (0:ℝ) ≤ Real.sqrt (Real.sqrt 3) := le_of_lt hsqrt3pos
    have h3 : (0:ℝ) ≤ (4*A)^A := Real.rpow_nonneg hAp.le A
    have h4 : (0:ℝ) ≤ (Real.log 2)^(-A) := Real.rpow_nonneg hlog2pos.le _
    have h5 : (0:ℝ) ≤ Real.sqrt (Real.sqrt 3) * (4*A)^A * (Real.log 2)^(-A) :=
      mul_nonneg (mul_nonneg h2 h3) h4
    linarith
  refine ⟨C, by linarith, ?_⟩
  intro Q t hQ ht
  have hst : 0 ≤ sHalf t := sHalf_nonneg t
  have hQpos : 0 < Q := by linarith
  rcases lt_or_ge Q 2 with hQ2 | hQ2
  · have hfl : ⌊Q⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      constructor <;> push_cast <;> linarith
    rw [hfl]
    have hfil : (Finset.Icc 1 1).filter (fun d => Squarefree d ∧ Nat.Coprime d t) = {1} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      constructor
      · simp [squarefree_one]
      · intro d hd
        simp only [Finset.mem_filter, Finset.mem_Icc] at hd
        omega
    rw [hfil, Finset.sum_singleton]
    have hp1 : prodKappa 1 = 1 := by simp [Work.LinnikAreas.Density4.prodKappa]
    rw [hp1, one_mul, one_mul, Nat.cast_one, div_one]
    have hlg : 0 ≤ (Real.log (2+Q))^(-A) := Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
    have hxy : 0 ≤ sHalf t * (Real.log (2 + Q))^(-A) := mul_nonneg hst hlg
    have hkey : sHalf t * (Real.log (2 + Q))^(-A)
        = C * sHalf t * (Real.log (2 + Q))^(-A)
          - (C - 1) * (sHalf t * (Real.log (2 + Q))^(-A)) := by ring
    rw [hkey]
    have h2 : (0:ℝ) ≤ (C - 1) * (sHalf t * (Real.log (2 + Q))^(-A)) := mul_nonneg hCnn hxy
    linarith
  · have hlog2Q : 0 < Real.log (2 + Q) := Real.log_pos (by linarith)
    set F : Finset ℕ := (Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Squarefree d ∧ Nat.Coprime d t)
      with hFdef
    set F1 : Finset ℕ := F.filter (fun d => (d:ℝ) * (d:ℝ) ≤ Q) with hF1def
    set F2 : Finset ℕ := F.filter (fun d => ¬ ((d:ℝ) * (d:ℝ) ≤ Q)) with hF2def
    have hmemF : ∀ d ∈ F, d ∈ Finset.Icc 1 ⌊Q⌋₊ ∧ Squarefree d ∧ Nat.Coprime d t := by
      intro d hd
      rw [hFdef] at hd
      exact Finset.mem_filter.mp hd
    have hsum1 : (∑ d ∈ F1, prodKappa d * sHalf d) ≤ 16 := by
      calc (∑ d ∈ F1, prodKappa d * sHalf d)
          ≤ ∑ d ∈ F1, ((Nat.divisors d).card : ℝ) / (d:ℝ)^(3/2:ℝ) := by
            apply Finset.sum_le_sum
            intro d hd
            exact prodKappa_mul_sHalf_le d (hmemF d (Finset.mem_filter.mp hd).1).2.1
        _ ≤ ∑ d ∈ Finset.Icc 1 ⌊Q⌋₊, ((Nat.divisors d).card : ℝ) / (d:ℝ)^(3/2:ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro d hd
              exact (hmemF d (Finset.mem_filter.mp hd).1).1
            · intro d hd _
              positivity
        _ ≤ 16 := tau_rpow_sum_bound ⌊Q⌋₊
    have hsum2 : (∑ d ∈ F2, prodKappa d * sHalf d) ≤ (Real.sqrt (Real.sqrt Q))⁻¹ * 16 := by
      have hQ14 : 0 < (Real.sqrt (Real.sqrt Q))⁻¹ :=
        inv_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hQpos))
      calc (∑ d ∈ F2, prodKappa d * sHalf d)
          ≤ ∑ d ∈ F2, ((Nat.divisors d).card : ℝ) / (d:ℝ)^2 := by
            apply Finset.sum_le_sum
            intro d hd
            exact prodKappa_mul_sHalf_le_sq d (hmemF d (Finset.mem_filter.mp hd).1).2.1
        _ ≤ ∑ d ∈ F2, (Real.sqrt (Real.sqrt Q))⁻¹ * (((Nat.divisors d).card : ℝ) / (d:ℝ)^(3/2:ℝ)) := by
            apply Finset.sum_le_sum
            intro d hd
            have hdF : d ∈ F := (Finset.mem_filter.mp hd).1
            obtain ⟨hdIcc, hdsq, hdcop⟩ := hmemF d hdF
            have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
            have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd1
            have hdd : ¬ ((d:ℝ) * (d:ℝ) ≤ Q) := (Finset.mem_filter.mp hd).2
            have hd2 : Q < (d:ℝ)^2 := by
              have h : ((d:ℝ)*(d:ℝ)) = (d:ℝ)^2 := by ring
              have h' : Q < ((d:ℝ)*(d:ℝ)) := lt_of_not_ge hdd
              linarith
            have hsq : Real.sqrt Q ≤ (d:ℝ) := by
              have h3 : Q ≤ (d:ℝ) * (d:ℝ) := by
                have h : (d:ℝ) * (d:ℝ) = (d:ℝ)^2 := by ring
                linarith
              have h1 : Real.sqrt Q ≤ Real.sqrt ((d:ℝ) * (d:ℝ)) := Real.sqrt_le_sqrt h3
              have h2 : Real.sqrt ((d:ℝ) * (d:ℝ)) = (d:ℝ) := by
                rw [show (d:ℝ) * (d:ℝ) = (d:ℝ)^2 by ring, Real.sqrt_sq hdpos.le]
              linarith
            have hkey : ((d:ℝ))^2 = (d:ℝ)^(3/2:ℝ) * Real.sqrt (d:ℝ) := by
              rw [← Real.rpow_natCast ((d:ℝ)) 2, Real.sqrt_eq_rpow, ← Real.rpow_add hdpos]
              norm_num
            have hsd : 0 < Real.sqrt (d:ℝ) := Real.sqrt_pos.mpr hdpos
            have hssq : 0 < Real.sqrt (Real.sqrt Q) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hQpos)
            have hstep : ((Nat.divisors d).card : ℝ) / (d:ℝ)^(3/2:ℝ) * (1/Real.sqrt (d:ℝ))
                = ((Nat.divisors d).card : ℝ) / (d:ℝ)^2 := by
              rw [div_mul_div_comm, mul_one, hkey]
            rw [← hstep]
            have hinv : 1/Real.sqrt (d:ℝ) ≤ (Real.sqrt (Real.sqrt Q))⁻¹ := by
              have h := one_div_le_one_div_of_le hssq (by
                rw [Real.sqrt_le_sqrt_iff hdpos.le]; exact hsq)
              simpa only [one_div] using h
            calc ((Nat.divisors d).card : ℝ) / (d:ℝ)^(3/2:ℝ) * (1/Real.sqrt (d:ℝ))
                ≤ ((Nat.divisors d).card : ℝ) / (d:ℝ)^(3/2:ℝ) * (Real.sqrt (Real.sqrt Q))⁻¹ :=
                  mul_le_mul_of_nonneg_left hinv
                    (div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hdpos.le _))
              _ = (Real.sqrt (Real.sqrt Q))⁻¹ * (((Nat.divisors d).card : ℝ) / (d:ℝ)^(3/2:ℝ)) := by ring
        _ = (Real.sqrt (Real.sqrt Q))⁻¹ * (∑ d ∈ F2, ((Nat.divisors d).card : ℝ) / (d:ℝ)^(3/2:ℝ)) := by
            rw [Finset.mul_sum]
        _ ≤ (Real.sqrt (Real.sqrt Q))⁻¹ * 16 := by
            apply mul_le_mul_of_nonneg_left _ hQ14.le
            calc (∑ d ∈ F2, ((Nat.divisors d).card : ℝ) / (d:ℝ)^(3/2:ℝ))
                ≤ ∑ d ∈ Finset.Icc 1 ⌊Q⌋₊, ((Nat.divisors d).card : ℝ) / (d:ℝ)^(3/2:ℝ) := by
                  apply Finset.sum_le_sum_of_subset_of_nonneg
                  · intro d hd
                    exact (hmemF d (Finset.mem_filter.mp hd).1).1
                  · intro d hd _
                    positivity
              _ ≤ 16 := tau_rpow_sum_bound ⌊Q⌋₊
    have hL2nn : (0:ℝ) ≤ (Real.log (2+Q))^(-A) := Real.rpow_nonneg hlog2Q.le _
    have h4nn : (0:ℝ) ≤ 4^A := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 4) A
    have hpart1 : (∑ d ∈ F1, prodKappa d * sHalf (d * t) * (Real.log (2 + Q / (d:ℝ)))^(-A))
        ≤ 4^A * (Real.log (2 + Q))^(-A) * sHalf t * 16 := by
      calc (∑ d ∈ F1, prodKappa d * sHalf (d * t) * (Real.log (2 + Q / (d:ℝ)))^(-A))
          ≤ ∑ d ∈ F1, prodKappa d * sHalf d * sHalf t * (4^A * (Real.log (2 + Q))^(-A)) := by
            apply Finset.sum_le_sum
            intro d hd
            have hdF : d ∈ F := (Finset.mem_filter.mp hd).1
            obtain ⟨hdIcc, hdsq, hdcop⟩ := hmemF d hdF
            have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
            have hdd : (d:ℝ) * (d:ℝ) ≤ Q := (Finset.mem_filter.mp hd).2
            have hmul : sHalf (d * t) = sHalf d * sHalf t := by
              rw [Work.LinnikAreas.Density4.sHalf, Work.LinnikAreas.Density4.sHalf,
                Work.LinnikAreas.Density4.sHalf]
              exact divisors_sqrtrecip_mul_coprime hdcop
            have hlg := log_div_rpow_le_small hA hQ2 hd1 hdd
            have hnn : (0:ℝ) ≤ prodKappa d * sHalf d * sHalf t :=
              mul_nonneg (mul_nonneg (prodKappa_nonneg' d) (sHalf_nonneg d)) hst
            rw [hmul,
              show prodKappa d * (sHalf d * sHalf t) * (Real.log (2 + Q / (d:ℝ)))^(-A)
                = prodKappa d * sHalf d * sHalf t * (Real.log (2 + Q / (d:ℝ)))^(-A) from by ring]
            exact mul_le_mul_of_nonneg_left hlg hnn
        _ = 4^A * (Real.log (2 + Q))^(-A) * sHalf t * (∑ d ∈ F1, prodKappa d * sHalf d) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d hd
            ring
        _ ≤ 4^A * (Real.log (2 + Q))^(-A) * sHalf t * 16 := by
            apply mul_le_mul_of_nonneg_left hsum1
            exact mul_nonneg (mul_nonneg h4nn hL2nn) hst
    have hpart2 : (∑ d ∈ F2, prodKappa d * sHalf (d * t) * (Real.log (2 + Q / (d:ℝ)))^(-A))
        ≤ (Real.log 2)^(-A) * sHalf t * ((Real.sqrt (Real.sqrt Q))⁻¹ * 16) := by
      calc (∑ d ∈ F2, prodKappa d * sHalf (d * t) * (Real.log (2 + Q / (d:ℝ)))^(-A))
          ≤ ∑ d ∈ F2, prodKappa d * sHalf d * sHalf t * ((Real.log 2)^(-A)) := by
            apply Finset.sum_le_sum
            intro d hd
            have hdF : d ∈ F := (Finset.mem_filter.mp hd).1
            obtain ⟨hdIcc, hdsq, hdcop⟩ := hmemF d hdF
            have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
            have hmul : sHalf (d * t) = sHalf d * sHalf t := by
              rw [Work.LinnikAreas.Density4.sHalf, Work.LinnikAreas.Density4.sHalf,
                Work.LinnikAreas.Density4.sHalf]
              exact divisors_sqrtrecip_mul_coprime hdcop
            have hlg := log_div_rpow_le_big hA hQ hd1
            have hnn : (0:ℝ) ≤ prodKappa d * sHalf d * sHalf t :=
              mul_nonneg (mul_nonneg (prodKappa_nonneg' d) (sHalf_nonneg d)) hst
            rw [hmul,
              show prodKappa d * (sHalf d * sHalf t) * (Real.log (2 + Q / (d:ℝ)))^(-A)
                = prodKappa d * sHalf d * sHalf t * (Real.log (2 + Q / (d:ℝ)))^(-A) from by ring]
            exact mul_le_mul_of_nonneg_left hlg hnn
        _ = (Real.log 2)^(-A) * sHalf t * (∑ d ∈ F2, prodKappa d * sHalf d) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro d hd
            ring
        _ ≤ (Real.log 2)^(-A) * sHalf t * ((Real.sqrt (Real.sqrt Q))⁻¹ * 16) := by
            apply mul_le_mul_of_nonneg_left hsum2
            exact mul_nonneg (Real.rpow_nonneg hlog2pos.le _) hst
    have hQ14le := inv_sqrt_sqrt_le_logpow A hA Q hQ
    have hcomb : (∑ d ∈ F, prodKappa d * sHalf (d * t) * (Real.log (2 + Q / (d:ℝ)))^(-A))
        = (∑ d ∈ F1, prodKappa d * sHalf (d * t) * (Real.log (2 + Q / (d:ℝ)))^(-A))
          + (∑ d ∈ F2, prodKappa d * sHalf (d * t) * (Real.log (2 + Q / (d:ℝ)))^(-A)) := by
      rw [hF1def, hF2def]
      rw [← Finset.sum_filter_add_sum_filter_not F (fun d => (d:ℝ)*(d:ℝ) ≤ Q)
        (fun d => prodKappa d * sHalf (d * t) * (Real.log (2 + Q / (d:ℝ)))^(-A))]
    rw [hcomb]
    refine (add_le_add (le_refl (∑ d ∈ F1, prodKappa d * sHalf (d * t) * (Real.log (2 + Q / (d:ℝ)))^(-A))) hpart2).trans ?_
    have hstep2 : (Real.log 2)^(-A) * sHalf t * ((Real.sqrt (Real.sqrt Q))⁻¹ * 16)
        ≤ (Real.log 2)^(-A) * sHalf t
            * (Real.sqrt (Real.sqrt 3) * (4*A)^A * (Real.log (2 + Q))^(-A) * 16) := by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (Real.rpow_nonneg hlog2pos.le _) hst)
      exact mul_le_mul_of_nonneg_right hQ14le (by norm_num)
    have hbk : 4^A * (Real.log (2 + Q))^(-A) * sHalf t * 16
        = 16 * (4:ℝ)^A * sHalf t * (Real.log (2 + Q))^(-A) := by ring
    have hb1 : (∑ d ∈ F1, prodKappa d * sHalf (d * t) * (Real.log (2 + Q / (d:ℝ)))^(-A))
        ≤ 16 * (4:ℝ)^A * sHalf t * (Real.log (2 + Q))^(-A) := hpart1.trans (le_of_eq hbk)
    refine (add_le_add hb1 hstep2).trans ?_
    have hkey : 16 * (4:ℝ)^A * sHalf t * (Real.log (2 + Q))^(-A)
          + (Real.log 2)^(-A) * sHalf t
            * (Real.sqrt (Real.sqrt 3) * (4*A)^A * (Real.log (2 + Q))^(-A) * 16)
        = C * sHalf t * (Real.log (2 + Q))^(-A) - sHalf t * (Real.log (2 + Q))^(-A) := by
      rw [hCdef]; ring
    rw [hkey]
    have hxy : 0 ≤ sHalf t * (Real.log (2 + Q))^(-A) := mul_nonneg hst hL2nn
    linarith

end

end Work.LinnikAreas.JutilaPieces
