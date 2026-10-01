import Mathlib
import Submission.Work.LinnikAreas.Density4.mu_kappa_log_sum
import Submission.Commons.Analysis.ExpLog.log_le_rpow_div

namespace Work.LinnikAreas.Density4

open Finset
open scoped BigOperators

noncomputable section

/-- `(log Q)^{-A} ≤ 2^A (log (2+Q))^{-A}` for `Q ≥ 2`. -/
private lemma log_pow_le_two_mul (A Q : ℝ) (hA : 0 < A) (hQ : 2 ≤ Q) :
    (Real.log Q) ^ (-A) ≤ (2:ℝ) ^ A * (Real.log (2 + Q)) ^ (-A) := by
  have hQpos : 0 < Q := by linarith
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hlogQnn : 0 ≤ Real.log Q := hlogQ.le
  have hlog2Q : 0 < Real.log (2 + Q) := Real.log_pos (by linarith)
  have hlog_le : Real.log (2 + Q) ≤ 2 * Real.log Q := by
    have h1 : Real.log (2 + Q) ≤ Real.log (2 * Q) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have h2 : Real.log 2 ≤ Real.log Q := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hpow : (Real.log (2 + Q)) ^ A ≤ (2:ℝ) ^ A * (Real.log Q) ^ A := by
    have h := Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hlog_le hA.le
    rwa [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hlogQnn] at h
  rw [Real.rpow_neg hlogQnn, Real.rpow_neg (Real.log_nonneg (by linarith))]
  rw [inv_eq_one_div, inv_eq_one_div, mul_one_div]
  rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hlogQ A) (Real.rpow_pos_of_pos hlog2Q A)]
  linarith [hpow]

/-- `(log 2)^{-A} · Q^{-1/4} ≤ (log 2)^{-A} · (4A)^A · 2^{1/4} · (log (2+Q))^{-A}` for `Q ≥ 2`. -/
private lemma inv_quarter_le_logpow (A Q : ℝ) (hA : 0 < A) (hQ : 2 ≤ Q) :
    (Real.log 2) ^ (-A) * Q ^ (-(1:ℝ)/4)
      ≤ (Real.log 2) ^ (-A) * (4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4) * (Real.log (2 + Q)) ^ (-A) := by
  have hQpos : 0 < Q := by linarith
  have hlog2Q : 0 < Real.log (2 + Q) := Real.log_pos (by linarith)
  have hQp : 0 < Q ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos hQpos _
  have hlogbound : (Real.log (2 + Q)) ^ A
      ≤ (4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4) * Q ^ ((1:ℝ)/4) := by
    have h1 : Real.log (2 + Q) ≤ 4*A * (2 + Q) ^ ((1:ℝ)/(4*A)) := by
      have h := Commons.Analysis.ExpLog.log_le_rpow_div (w := 2 + Q) (a := (1:ℝ)/(4*A))
        (by linarith) (by positivity)
      have h2 : (2 + Q) ^ ((1:ℝ)/(4*A)) / ((1:ℝ)/(4*A))
          = 4*A * (2 + Q) ^ ((1:ℝ)/(4*A)) := by
        rw [one_div, div_inv_eq_mul]; ring
      linarith [h, h2]
    have hp : (Real.log (2 + Q)) ^ A ≤ (4*A * (2 + Q) ^ ((1:ℝ)/(4*A))) ^ A :=
      Real.rpow_le_rpow (Real.log_nonneg (by linarith)) h1 hA.le
    have hq : (4*A * (2 + Q) ^ ((1:ℝ)/(4*A))) ^ A
        = (4*A) ^ A * (2 + Q) ^ ((1:ℝ)/4) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg (by linarith) _)]
      congr 1
      rw [← Real.rpow_mul (by linarith : (0:ℝ) ≤ 2 + Q)]
      congr 1
      field_simp
    rw [hq] at hp
    have hr : (2 + Q) ^ ((1:ℝ)/4) ≤ (2:ℝ) ^ ((1:ℝ)/4) * Q ^ ((1:ℝ)/4) := by
      have h4 : (2 + Q) ^ ((1:ℝ)/4) ≤ (2*Q) ^ ((1:ℝ)/4) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      rwa [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hQpos.le] at h4
    calc (Real.log (2 + Q)) ^ A ≤ (4*A) ^ A * (2 + Q) ^ ((1:ℝ)/4) := hp
      _ ≤ (4*A) ^ A * ((2:ℝ) ^ ((1:ℝ)/4) * Q ^ ((1:ℝ)/4)) :=
          mul_le_mul_of_nonneg_left hr (Real.rpow_nonneg (by positivity) _)
      _ = (4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4) * Q ^ ((1:ℝ)/4) := by ring
  have hQinv : Q ^ (-(1:ℝ)/4) ≤ (4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4) * (Real.log (2 + Q)) ^ (-A) := by
    rw [show (-(1:ℝ)/4) = -((1:ℝ)/4) by ring, Real.rpow_neg hQpos.le]
    rw [Real.rpow_neg hlog2Q.le, inv_eq_one_div, inv_eq_one_div, mul_one_div]
    rw [div_le_div_iff₀ hQp (Real.rpow_pos_of_pos hlog2Q A)]
    linarith [hlogbound]
  calc (Real.log 2) ^ (-A) * Q ^ (-(1:ℝ)/4)
      ≤ (Real.log 2) ^ (-A) * ((4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4) * (Real.log (2 + Q)) ^ (-A)) :=
        mul_le_mul_of_nonneg_left hQinv (Real.rpow_nonneg (Real.log_nonneg (by norm_num)) _)
    _ = (Real.log 2) ^ (-A) * (4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4) * (Real.log (2 + Q)) ^ (-A) := by ring

/-- Arbitrary-exponent generalisation of `kappa_error_sum_self` (which has exponent `-3`): the
`κ`-error sum against `Θ`, with `sigma_{-1/2}(t) = sHalf t = Σ_{d | t} 1/√d` factored out. -/
theorem kappa_error_sum_pow (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ) (t : ℕ), 1 ≤ Q → 1 ≤ t →
      (∑ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Squarefree d ∧ Nat.Coprime d t),
          Work.LinnikAreas.Density4.prodKappa d * Work.LinnikAreas.Density4.sHalf (d * t) *
            (Real.log (2 + Q / (d : ℝ))) ^ (-A))
        ≤ C * Work.LinnikAreas.Density4.sHalf t * (Real.log (2 + Q)) ^ (-A) := by
  refine ⟨max 1 (16 * (2:ℝ)^A * (2:ℝ)^A
      + 16 * (Real.log 2) ^ (-A) * (4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4)) + 1, by positivity, ?_⟩
  intro Q t hQ ht
  have hsHnn : 0 ≤ sHalf t := sHalf_nonneg t
  have hCle : (1:ℝ) ≤ max 1 (16 * (2:ℝ)^A * (2:ℝ)^A
      + 16 * (Real.log 2) ^ (-A) * (4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4)) + 1 :=
    le_trans (le_max_left _ _) (le_add_of_nonneg_right (by norm_num))
  set D : Finset ℕ := (Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Squarefree d ∧ Nat.Coprime d t) with hD
  rcases lt_or_ge Q 2 with hQ2 | hQ2
  · -- small `Q`: `⌊Q⌋₊ = 1` and the sum is a single term
    have hN1 : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by simpa using hQ)
    have hNle : ⌊Q⌋₊ ≤ 1 := by
      have h2 : ¬ ((2:ℕ) ≤ ⌊Q⌋₊) := by
        intro hh
        have h3 : (2:ℝ) ≤ Q := (Nat.le_floor_iff (show (0:ℝ) ≤ Q by linarith)).mp hh
        exact absurd h3 (not_le.mpr hQ2)
      omega
    have hNeq : ⌊Q⌋₊ = 1 := le_antisymm hNle hN1
    have hD1 : D = {1} := by
      rw [hD, hNeq]
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, -⟩; omega
      · rintro rfl
        exact ⟨⟨le_rfl, le_rfl⟩, squarefree_one, Nat.coprime_one_left t⟩
    rw [hD1, Finset.sum_singleton]
    have hp1 : prodKappa 1 = 1 := by simp [prodKappa]
    simp only [hp1, one_mul, Nat.one_mul, Nat.cast_one, div_one]
    have hLnn : 0 ≤ Real.log (2 + Q) ^ (-A) :=
      Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
    have hXn : 0 ≤ sHalf t * Real.log (2 + Q) ^ (-A) := mul_nonneg hsHnn hLnn
    calc sHalf t * Real.log (2 + Q) ^ (-A)
        = (sHalf t * Real.log (2 + Q) ^ (-A)) * 1 := by ring
      _ ≤ (sHalf t * Real.log (2 + Q) ^ (-A))
            * (max 1 (16 * (2:ℝ)^A * (2:ℝ)^A
              + 16 * (Real.log 2) ^ (-A) * (4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4)) + 1) :=
          mul_le_mul_of_nonneg_left hCle hXn
      _ = (max 1 (16 * (2:ℝ)^A * (2:ℝ)^A
              + 16 * (Real.log 2) ^ (-A) * (4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4)) + 1)
            * sHalf t * Real.log (2 + Q) ^ (-A) := by ring
  · -- `Q ≥ 2`
    have hQpos : 0 < Q := by linarith
    have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
    have hlogQnn : 0 ≤ Real.log Q := hlogQ.le
    have hN1 : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by simpa using hQ)
    -- factor `sHalf t`
    have hfac : ∀ d ∈ D, prodKappa d * sHalf (d*t) * (Real.log (2 + Q/(d:ℝ)))^(-A)
        = sHalf t * (prodKappa d * sHalf d * (Real.log (2 + Q/(d:ℝ)))^(-A)) := by
      intro d hd
      rw [hD, Finset.mem_filter] at hd
      obtain ⟨-, hdsq, hdcop⟩ := hd
      have h := divisors_sqrtrecip_mul_coprime hdcop
      rw [show sHalf (d*t) = sHalf d * sHalf t by simpa only [sHalf] using h]
      ring
    have hexp : (∑ d ∈ D, prodKappa d * sHalf (d*t) * (Real.log (2 + Q/(d:ℝ)))^(-A))
        = sHalf t * ∑ d ∈ D, prodKappa d * sHalf d * (Real.log (2 + Q/(d:ℝ)))^(-A) := by
      rw [Finset.sum_congr rfl hfac, Finset.mul_sum]
    rw [hexp]
    have hsplit : (∑ d ∈ D, prodKappa d * sHalf d * (Real.log (2 + Q/(d:ℝ)))^(-A))
        = (∑ d ∈ D.filter (fun d : ℕ => (d:ℝ)^2 ≤ Q),
              prodKappa d * sHalf d * (Real.log (2 + Q/(d:ℝ)))^(-A))
          + (∑ d ∈ D.filter (fun d : ℕ => ¬ (d:ℝ)^2 ≤ Q),
              prodKappa d * sHalf d * (Real.log (2 + Q/(d:ℝ)))^(-A)) := by
      rw [← Finset.sum_filter_add_sum_filter_not D (fun d : ℕ => (d:ℝ)^2 ≤ Q)]
    rw [hsplit]
    -- part 1: `d*d ≤ Q`
    have hpart1 : (∑ d ∈ D.filter (fun d : ℕ => (d:ℝ)^2 ≤ Q),
          prodKappa d * sHalf d * (Real.log (2 + Q/(d:ℝ)))^(-A))
        ≤ 16 * (2:ℝ)^A * (2:ℝ)^A * Real.log (2 + Q) ^ (-A) := by
      have hsum : (∑ d ∈ D.filter (fun d : ℕ => (d:ℝ)^2 ≤ Q), prodKappa d * sHalf d) ≤ 16 := by
        calc (∑ d ∈ D.filter (fun d : ℕ => (d:ℝ)^2 ≤ Q), prodKappa d * sHalf d)
            ≤ ∑ d ∈ D.filter (fun d : ℕ => (d:ℝ)^2 ≤ Q),
                ((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ) := by
              refine Finset.sum_le_sum (fun d hd => ?_)
              obtain ⟨hdD, -⟩ := Finset.mem_filter.mp hd
              obtain ⟨-, hdsq, -⟩ := Finset.mem_filter.mp hdD
              exact prodKappa_mul_sHalf_le d hdsq
          _ ≤ ∑ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun d => Squarefree d),
                ((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ) := by
              rw [hD]
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro d hd
                simp only [Finset.mem_filter] at hd ⊢
                exact ⟨hd.1.1, hd.1.2.1⟩
              · intro d hd _
                exact div_nonneg (by positivity) (by positivity)
          _ ≤ ∑ d ∈ Finset.Icc 1 ⌊Q⌋₊,
                ((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ) := by
              refine Finset.sum_le_sum_of_subset_of_nonneg
                (f := fun d => ((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ))
                (Finset.filter_subset _ _) ?_
              intro d hd _
              exact div_nonneg (by positivity) (by positivity)
          _ ≤ 16 := tau_rpow_sum_bound ⌊Q⌋₊
      have hstep : (∑ d ∈ D.filter (fun d : ℕ => (d:ℝ)^2 ≤ Q),
            prodKappa d * sHalf d * (Real.log (2 + Q/(d:ℝ)))^(-A))
          ≤ ∑ d ∈ D.filter (fun d : ℕ => (d:ℝ)^2 ≤ Q),
              prodKappa d * sHalf d * ((2:ℝ)^A * Real.log Q ^ (-A)) := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        obtain ⟨hdD, hd2⟩ := Finset.mem_filter.mp hd
        obtain ⟨hdIcc, -, -⟩ := Finset.mem_filter.mp hdD
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
        have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
        have hd2R : (d:ℝ)^2 ≤ Q := hd2
        have hdle : (d:ℝ) ≤ Real.sqrt Q := (Real.le_sqrt (by positivity) hQpos.le).mpr hd2R
        have hsq : Real.sqrt Q ≤ Q / (d:ℝ) := by
          rw [le_div_iff₀ hdpos]
          calc Real.sqrt Q * (d:ℝ) ≤ Real.sqrt Q * Real.sqrt Q :=
                mul_le_mul_of_nonneg_left hdle (Real.sqrt_nonneg Q)
            _ = Q := by rw [← pow_two]; exact Real.sq_sqrt hQpos.le
        have hlogle : Real.log Q ≤ 2 * Real.log (2 + Q/(d:ℝ)) := by
          have h1 : Real.log (Real.sqrt Q) ≤ Real.log (2 + Q/(d:ℝ)) :=
            Real.log_le_log (Real.sqrt_pos.mpr hQpos) (by linarith)
          rw [Real.log_sqrt hQpos.le] at h1
          linarith
        have hpow : (Real.log Q)^A ≤ (2:ℝ)^A * (Real.log (2 + Q/(d:ℝ)))^A := by
          have h := Real.rpow_le_rpow hlogQnn hlogle hA.le
          rwa [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.log_nonneg (by linarith))] at h
        have hLle : (Real.log (2 + Q/(d:ℝ)))^(-A) ≤ (2:ℝ)^A * (Real.log Q)^(-A) := by
          have hLpos : 0 < Real.log (2 + Q/(d:ℝ)) := Real.log_pos (by linarith)
          rw [Real.rpow_neg (Real.log_nonneg (by linarith)), Real.rpow_neg hlogQnn]
          rw [inv_eq_one_div, inv_eq_one_div, mul_one_div]
          rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hLpos A) (Real.rpow_pos_of_pos hlogQ A)]
          linarith [hpow]
        exact mul_le_mul_of_nonneg_left hLle (mul_nonneg (prodKappa_nonneg d) (sHalf_nonneg d))
      refine hstep.trans ?_
      have hgoal2 : (∑ d ∈ D.filter (fun d : ℕ => (d:ℝ)^2 ≤ Q),
            prodKappa d * sHalf d * ((2:ℝ)^A * Real.log Q ^ (-A)))
          = (2:ℝ)^A * Real.log Q ^ (-A)
            * (∑ d ∈ D.filter (fun d : ℕ => (d:ℝ)^2 ≤ Q), prodKappa d * sHalf d) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun d hd => ?_)
        ring
      rw [hgoal2]
      have hnn : (0:ℝ) ≤ (2:ℝ)^A * Real.log Q ^ (-A) :=
        mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hlogQnn _)
      calc (2:ℝ)^A * Real.log Q ^ (-A)
            * (∑ d ∈ D.filter (fun d : ℕ => (d:ℝ)^2 ≤ Q), prodKappa d * sHalf d)
          ≤ (2:ℝ)^A * Real.log Q ^ (-A) * 16 := mul_le_mul_of_nonneg_left hsum hnn
        _ ≤ (2:ℝ)^A * (2:ℝ)^A * Real.log (2 + Q) ^ (-A) * 16 := by
            have h2Ap : (0:ℝ) ≤ (2:ℝ)^A := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) A
            calc (2:ℝ)^A * Real.log Q ^ (-A) * 16
                = (2:ℝ)^A * (Real.log Q ^ (-A) * 16) := by ring
              _ ≤ (2:ℝ)^A * ((2:ℝ)^A * Real.log (2 + Q) ^ (-A) * 16) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right (log_pow_le_two_mul A Q hA hQ2)
                      (by norm_num : (0:ℝ) ≤ 16)) h2Ap
              _ = (2:ℝ)^A * (2:ℝ)^A * Real.log (2 + Q) ^ (-A) * 16 := by ring
        _ = 16 * (2:ℝ)^A * (2:ℝ)^A * Real.log (2 + Q) ^ (-A) := by ring
    -- part 2: `¬ d*d ≤ Q`
    have hpart2 : (∑ d ∈ D.filter (fun d : ℕ => ¬ (d:ℝ)^2 ≤ Q),
          prodKappa d * sHalf d * (Real.log (2 + Q/(d:ℝ)))^(-A))
        ≤ 16 * (Real.log 2) ^ (-A) * Q ^ (-(1:ℝ)/4) := by
      have hstep : (∑ d ∈ D.filter (fun d : ℕ => ¬ (d:ℝ)^2 ≤ Q),
            prodKappa d * sHalf d * (Real.log (2 + Q/(d:ℝ)))^(-A))
          ≤ ∑ d ∈ D.filter (fun d : ℕ => ¬ (d:ℝ)^2 ≤ Q),
              ((Nat.divisors d).card : ℝ)/(d:ℝ)^2 * (Real.log 2) ^ (-A) := by
        refine Finset.sum_le_sum (fun d hd => ?_)
        obtain ⟨hdD, hd2⟩ := Finset.mem_filter.mp hd
        obtain ⟨hdIcc, hdsq, -⟩ := Finset.mem_filter.mp hdD
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
        have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
        have hqd : (0:ℝ) ≤ Q/(d:ℝ) := div_nonneg hQpos.le hdpos.le
        have hLpos : 0 < Real.log (2 + Q/(d:ℝ)) := Real.log_pos (by linarith)
        have hLle : (Real.log (2 + Q/(d:ℝ)))^(-A) ≤ (Real.log 2)^(-A) := by
          have h2 : Real.log 2 ≤ Real.log (2 + Q/(d:ℝ)) := Real.log_le_log (by norm_num) (by linarith)
          exact Real.rpow_le_rpow_of_nonpos (Real.log_pos (by norm_num)) h2 (by linarith)
        calc prodKappa d * sHalf d * (Real.log (2 + Q/(d:ℝ)))^(-A)
            ≤ ((Nat.divisors d).card : ℝ)/(d:ℝ)^2 * (Real.log (2 + Q/(d:ℝ)))^(-A) :=
              mul_le_mul_of_nonneg_right (prodKappa_mul_sHalf_le_sq d hdsq)
                (Real.rpow_nonneg hLpos.le (-A))
          _ ≤ ((Nat.divisors d).card : ℝ)/(d:ℝ)^2 * (Real.log 2)^(-A) :=
              mul_le_mul_of_nonneg_left hLle (by positivity)
      refine hstep.trans ?_
      have hQ4pos : 0 < Q ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos hQpos _
      have hper : ∀ d ∈ D.filter (fun d : ℕ => ¬ (d:ℝ)^2 ≤ Q),
          ((Nat.divisors d).card : ℝ)/(d:ℝ)^2 * (Real.log 2) ^ (-A)
            ≤ (Real.log 2) ^ (-A) * (Q ^ (-(1:ℝ)/4))
                * (((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ)) := by
        intro d hd
        obtain ⟨hdD, hd2⟩ := Finset.mem_filter.mp hd
        obtain ⟨hdIcc, -, -⟩ := Finset.mem_filter.mp hdD
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
        have hdpos : (0:ℝ) < (d:ℝ) := by exact_mod_cast (by omega : 0 < d)
        have hd2R : (Q:ℝ) < (d:ℝ)^2 := not_le.mp hd2
        have hsqrt : Real.sqrt Q < (d:ℝ) := by
          rw [Real.sqrt_lt' (by positivity)]
          exact hd2R
        have hquarter : (1:ℝ)/Real.sqrt (d:ℝ) ≤ Q ^ (-(1:ℝ)/4) := by
          have hqle : Q ^ ((1:ℝ)/4) ≤ Real.sqrt (d:ℝ) := by
            have heq : Q ^ ((1:ℝ)/4) = Real.sqrt (Real.sqrt Q) := by
              rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hQpos.le]
              norm_num
            rw [heq]
            exact Real.sqrt_le_sqrt (le_of_lt hsqrt)
          rw [show Q ^ (-(1:ℝ)/4) = 1 / Q ^ ((1:ℝ)/4) by
            rw [show (-(1:ℝ)/4) = -((1:ℝ)/4) by ring, Real.rpow_neg hQpos.le, inv_eq_one_div]]
          exact one_div_le_one_div_of_le hQ4pos hqle
        have heq : ((Nat.divisors d).card : ℝ)/(d:ℝ)^2
            = ((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ) * (1/Real.sqrt (d:ℝ)) := by
          have hsq : (d:ℝ)^2 = (d:ℝ)^(3/2 : ℝ) * Real.sqrt (d:ℝ) := by
            rw [← Real.rpow_natCast ((d:ℝ)) 2, Real.sqrt_eq_rpow, ← Real.rpow_add hdpos]
            norm_num
          have h1 : ((d:ℝ)^(3/2 : ℝ)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hdpos _)
          have h2 : (Real.sqrt (d:ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hdpos)
          rw [hsq]
          field_simp
        calc ((Nat.divisors d).card : ℝ)/(d:ℝ)^2 * (Real.log 2) ^ (-A)
            = (Real.log 2) ^ (-A) * (((Nat.divisors d).card : ℝ)/(d:ℝ)^2) := by ring
          _ = (Real.log 2) ^ (-A) * (((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ)
                * (1/Real.sqrt (d:ℝ))) := by rw [heq]
          _ ≤ (Real.log 2) ^ (-A) * (((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ)
                * Q ^ (-(1:ℝ)/4)) := by
              apply mul_le_mul_of_nonneg_left _
                (Real.rpow_nonneg (Real.log_nonneg (by norm_num)) _)
              exact mul_le_mul_of_nonneg_left hquarter (by positivity)
          _ = (Real.log 2) ^ (-A) * (Q ^ (-(1:ℝ)/4))
                * (((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ)) := by ring
      have hsub : D.filter (fun d : ℕ => ¬ (d:ℝ)^2 ≤ Q) ⊆ Finset.Icc 1 ⌊Q⌋₊ := by
        intro d hd
        exact (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1
      calc (∑ d ∈ D.filter (fun d : ℕ => ¬ (d:ℝ)^2 ≤ Q),
              ((Nat.divisors d).card : ℝ)/(d:ℝ)^2 * (Real.log 2) ^ (-A))
          ≤ ∑ d ∈ D.filter (fun d : ℕ => ¬ (d:ℝ)^2 ≤ Q),
              (Real.log 2) ^ (-A) * (Q ^ (-(1:ℝ)/4))
                * (((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ)) := Finset.sum_le_sum hper
        _ = (Real.log 2) ^ (-A) * (Q ^ (-(1:ℝ)/4))
              * (∑ d ∈ D.filter (fun d : ℕ => ¬ (d:ℝ)^2 ≤ Q),
                  ((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ)) := by
              rw [Finset.mul_sum]
        _ ≤ (Real.log 2) ^ (-A) * (Q ^ (-(1:ℝ)/4)) * 16 := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact (Finset.sum_le_sum_of_subset_of_nonneg
                  (f := fun d => ((Nat.divisors d).card : ℝ)/(d:ℝ)^(3/2 : ℝ)) hsub
                (fun d hd _ => div_nonneg (by positivity) (by positivity))).trans
                (tau_rpow_sum_bound ⌊Q⌋₊)
        _ = 16 * (Real.log 2) ^ (-A) * Q ^ (-(1:ℝ)/4) := by ring
    -- combine
    have hLnn : (0:ℝ) ≤ Real.log (2 + Q) ^ (-A) :=
      Real.rpow_nonneg (Real.log_nonneg (by linarith : (1:ℝ) ≤ 2 + Q)) (-A)
    have hbook := inv_quarter_le_logpow A Q hA hQ2
    have hb : 16 * (Real.log 2) ^ (-A) * Q ^ (-(1:ℝ)/4)
        ≤ 16 * (Real.log 2) ^ (-A) * (4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4)
          * Real.log (2 + Q) ^ (-A) := by
      calc 16 * (Real.log 2) ^ (-A) * Q ^ (-(1:ℝ)/4)
          = 16 * ((Real.log 2) ^ (-A) * Q ^ (-(1:ℝ)/4)) := by ring
        _ ≤ 16 * ((Real.log 2) ^ (-A) * (4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4)
              * Real.log (2 + Q) ^ (-A)) :=
            mul_le_mul_of_nonneg_left hbook (by norm_num)
        _ = 16 * (Real.log 2) ^ (-A) * (4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4)
              * Real.log (2 + Q) ^ (-A) := by ring
    have hK : 16 * (2:ℝ)^A * (2:ℝ)^A
          + 16 * (Real.log 2) ^ (-A) * (4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4)
        ≤ max 1 (16 * (2:ℝ)^A * (2:ℝ)^A
          + 16 * (Real.log 2) ^ (-A) * (4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4)) + 1 :=
      le_trans (le_max_right _ _) (le_add_of_nonneg_right (by norm_num))
    have hsplit2 : (∑ d ∈ D.filter (fun d : ℕ => (d:ℝ)^2 ≤ Q),
            prodKappa d * sHalf d * (Real.log (2 + Q/(d:ℝ)))^(-A))
          + (∑ d ∈ D.filter (fun d : ℕ => ¬ (d:ℝ)^2 ≤ Q),
            prodKappa d * sHalf d * (Real.log (2 + Q/(d:ℝ)))^(-A))
        ≤ (16 * (2:ℝ)^A * (2:ℝ)^A
            + 16 * (Real.log 2) ^ (-A) * (4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4))
          * Real.log (2 + Q) ^ (-A) := by
      refine (add_le_add hpart1 hpart2).trans ?_
      refine (add_le_add le_rfl hb).trans ?_
      exact le_of_eq (by ring)
    refine (mul_le_mul_of_nonneg_left hsplit2 hsHnn).trans ?_
    calc sHalf t * ((16 * (2:ℝ)^A * (2:ℝ)^A
              + 16 * (Real.log 2) ^ (-A) * (4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4))
            * Real.log (2 + Q) ^ (-A))
        = (16 * (2:ℝ)^A * (2:ℝ)^A
              + 16 * (Real.log 2) ^ (-A) * (4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4))
          * (sHalf t * Real.log (2 + Q) ^ (-A)) := by ring
      _ ≤ (max 1 (16 * (2:ℝ)^A * (2:ℝ)^A
              + 16 * (Real.log 2) ^ (-A) * (4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4)) + 1)
          * (sHalf t * Real.log (2 + Q) ^ (-A)) :=
          mul_le_mul_of_nonneg_right hK (mul_nonneg hsHnn hLnn)
      _ = (max 1 (16 * (2:ℝ)^A * (2:ℝ)^A
              + 16 * (Real.log 2) ^ (-A) * (4*A) ^ A * (2:ℝ) ^ ((1:ℝ)/4)) + 1)
          * sHalf t * Real.log (2 + Q) ^ (-A) := by ring

end

end Work.LinnikAreas.Density4
