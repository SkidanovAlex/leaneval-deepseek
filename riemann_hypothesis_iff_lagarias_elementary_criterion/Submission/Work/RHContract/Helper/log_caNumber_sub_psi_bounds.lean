import Mathlib
import Submission.Work.RHContract.Corpus
import Submission.Work.RHContract.A.CaDeltaDefs
import Submission.Work.RHContract.A.ca_delta_nonneg
import Submission.Work.RHContract.A.caLevel_le
import Submission.Work.RHContract.A.psi_ge_sum_theta
import Submission.Work.RHContract.A.theta_le_self_small
import Submission.Work.RHContract.A.theta_ge_frac_small

/-!
# `Work.RHContract.Helper.log_caNumber_sub_psi_bounds`

For a colossally abundant number `N_ε` with largest prime factor `ξ = ξ(ε) ≥ 1530` one has

  `0 ≤ log N_ε − ψ(ξ) ≤ 4 √ξ`.

The lower bound is `Work.RHContract.A.ca_delta_nonneg` (every prime `p ≤ ξ` divides
`lcm(1,…,ξ)` to a power at most its exponent in `N_ε`).

The upper bound is the `θ`-level decomposition of `log N_ε` (`Robin.caLogN_eq_sum_theta`)
together with the level bound `caLevel ε k ≤ (1.23 k ξ)^{1/k}` (`A.caLevel_le`) and the
purely numeric estimate `caDelta_aux` proved below from the step functions `caU`, `caL`
of `Submission.Work.RHContract.A.CaDeltaDefs`.
-/

open scoped BigOperators

namespace Work.RHContract.Helper

noncomputable section

open Work.RHContract.A

/-! ## elementary facts about `caU`, `caL` -/

private lemma caU_le_10987 (t : ℝ) (ht : 0 ≤ t) : caU t ≤ 1.0987 * t := by
  unfold caU
  split_ifs with h1 h2
  · nlinarith
  · nlinarith
  · have h3 : Real.log 3 ≤ 1.0987 := by linarith [Real.log_three_lt_d9]
    nlinarith

private lemma caU_eq_self' {t : ℝ} (h1 : 2 ≤ t) (h2 : t ≤ 1530) : caU t = t := by
  unfold caU; rw [if_neg (not_lt.mpr h1), if_pos h2]

private lemma caU_eq_log3 {t : ℝ} (h : 1530 < t) : caU t = Real.log 3 * t := by
  unfold caU; rw [if_neg (by linarith), if_neg (by linarith)]

private lemma caU_eq_zero' {t : ℝ} (h : t < 2) : caU t = 0 := by
  unfold caU; rw [if_pos h]

private lemma caL_ge_07 {t : ℝ} (ht : 39 ≤ t) : 0.7 * t ≤ caL t := by
  unfold caL
  rw [if_neg (by linarith : ¬ t < 3), if_neg (by linarith : ¬ t < 39)]
  split_ifs <;> nlinarith

/-! ## the `k = 2` term -/

private lemma T2_bound (ξ : ℝ) (hξ : 1530 ≤ ξ) :
    caU ((1.23 * 2 * ξ) ^ (1 / 2 : ℝ)) - caL (ξ ^ (1 / 2 : ℝ)) ≤ 1.03 * Real.sqrt ξ := by
  have hξ0 : 0 < ξ := by linarith
  have h1 : (1.23 * 2 * ξ) = 2.46 * ξ := by ring
  rw [h1]
  have h2 : ((2.46 * ξ) ^ (1 / 2 : ℝ)) = Real.sqrt (2.46 * ξ) := by rw [Real.sqrt_eq_rpow]
  have h3 : (ξ ^ (1 / 2 : ℝ)) = Real.sqrt ξ := by rw [Real.sqrt_eq_rpow]
  rw [h2, h3]
  have hY : Real.sqrt (2.46 * ξ) ≤ 1.5685 * Real.sqrt ξ := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1.5685 * Real.sqrt ξ)]
    apply Real.sqrt_le_sqrt
    rw [mul_pow, Real.sq_sqrt hξ0.le]
    nlinarith
  have hY2 : 2 ≤ Real.sqrt (2.46 * ξ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  have hU : caU (Real.sqrt (2.46 * ξ)) ≤ 1.724 * Real.sqrt ξ := by
    rcases le_or_gt (Real.sqrt (2.46 * ξ)) 1530 with h | h
    · rw [caU_eq_self' hY2 h]; linarith
    · rw [caU_eq_log3 h]
      have h3 : Real.log 3 ≤ 1.0987 := by linarith [Real.log_three_lt_d9]
      nlinarith [hY, Real.sqrt_nonneg ξ]
  have hL : 0.7 * Real.sqrt ξ ≤ caL (Real.sqrt ξ) := by
    apply caL_ge_07
    rw [Real.le_sqrt (by norm_num) hξ0.le]; nlinarith
  linarith

/-! ## per-`k` root bounds -/

private lemma ak_le_155 (k : ℕ) (hk : k ∈ Finset.Icc (3:ℕ) 14) :
    (1.23 * (k : ℝ)) ^ (1 / (k : ℝ)) ≤ 1.55 := by
  have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk14 : k ≤ 14 := (Finset.mem_Icc.mp hk).2
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  refine (Real.rpow_le_rpow_iff (x := (1.23 * (k : ℝ)) ^ (1 / (k : ℝ))) (y := 1.55)
    (z := (k : ℝ)) (by positivity) (by norm_num) hk0).mp ?_
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1.23 * (k : ℝ)) (1 / (k : ℝ)) (k : ℝ)]
  have h2 : (1 / (k : ℝ)) * (k : ℝ) = 1 := by field_simp
  rw [h2, Real.rpow_one, Real.rpow_natCast]
  interval_cases k <;> norm_num

private lemma ak_le_125 (k : ℕ) (hk : 15 ≤ k) :
    (1.23 * (k : ℝ)) ^ (1 / (k : ℝ)) ≤ 1.25 := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  refine (Real.rpow_le_rpow_iff (x := (1.23 * (k : ℝ)) ^ (1 / (k : ℝ))) (y := 1.25)
    (z := (k : ℝ)) (by positivity) (by norm_num) hk0).mp ?_
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1.23 * (k : ℝ)) (1 / (k : ℝ)) (k : ℝ)]
  have h2 : (1 / (k : ℝ)) * (k : ℝ) = 1 := by field_simp
  rw [h2, Real.rpow_one, Real.rpow_natCast]
  -- 1.23 * k ≤ 1.25 ^ k for k ≥ 15
  have key : ∀ j : ℕ, 15 ≤ j → (1.23 : ℝ) * j ≤ 1.25 ^ j := by
    intro j hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_or_ge j 15 with h | h
      · have : j = 14 := by omega
        subst this; norm_num
      · have ih' := ih h
        have hle : (1.23 : ℝ) * ((j : ℝ) + 1) ≤ 1.25 * ((1.23 : ℝ) * j) := by
          have hj15 : (15 : ℝ) ≤ (j : ℝ) := by exact_mod_cast h
          nlinarith
        have hcast : (1.23 : ℝ) * ((j + 1 : ℕ) : ℝ) = (1.23 : ℝ) * ((j : ℝ) + 1) := by push_cast; ring
        rw [hcast]
        calc (1.23 : ℝ) * ((j : ℝ) + 1) ≤ 1.25 * ((1.23 : ℝ) * (j : ℝ)) := hle
          _ ≤ 1.25 * 1.25 ^ j := by linarith
          _ = 1.25 ^ (j + 1) := by rw [pow_succ]; ring
  exact key k hk


/-! ## root bounds for the middle range -/

private lemma rpow_eighth_ge {ξ : ℝ} (hξ : 1530 ≤ ξ) : (5 / 2 : ℝ) ≤ ξ ^ (1 / 8 : ℝ) := by
  have h1 : (5 / 2 : ℝ) ≤ (1530 : ℝ) ^ (1 / 8 : ℝ) := by
    have h2 : ((5 / 2 : ℝ)) ^ (8 : ℝ) ≤ ((1530 : ℝ) ^ (1 / 8 : ℝ)) ^ (8 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1530), show (1 / 8 : ℝ) * 8 = 1 by norm_num,
        Real.rpow_one]
      norm_num
    exact (Real.rpow_le_rpow_iff (by norm_num) (by positivity) (by norm_num : (0 : ℝ) < 8)).mp h2
  exact le_trans h1 (Real.rpow_le_rpow (by norm_num) hξ (by norm_num))

private lemma rpow_sixth_ge {ξ : ℝ} (hξ : 1530 ≤ ξ) : (10 / 3 : ℝ) ≤ ξ ^ (1 / 6 : ℝ) := by
  have h1 : (10 / 3 : ℝ) ≤ (1530 : ℝ) ^ (1 / 6 : ℝ) := by
    have h2 : ((10 / 3 : ℝ)) ^ (6 : ℝ) ≤ ((1530 : ℝ) ^ (1 / 6 : ℝ)) ^ (6 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1530), show (1 / 6 : ℝ) * 6 = 1 by norm_num,
        Real.rpow_one]
      norm_num
    exact (Real.rpow_le_rpow_iff (by norm_num) (by positivity) (by norm_num : (0 : ℝ) < 6)).mp h2
  exact le_trans h1 (Real.rpow_le_rpow (by norm_num) hξ (by norm_num))

private lemma root_le_quarter {ξ : ℝ} (hξ : 1530 ≤ ξ) {k : ℕ} (h4 : 4 ≤ k) (h7 : k ≤ 7) :
    ξ ^ (1 / (k : ℝ)) ≤ ξ ^ (1 / 4 : ℝ) := by
  apply Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ ξ)
  exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) (by exact_mod_cast h4)

private lemma root_le_fifth {ξ : ℝ} (hξ : 1530 ≤ ξ) {k : ℕ} (h8 : 8 ≤ k) (h11 : k ≤ 11) :
    ξ ^ (1 / (k : ℝ)) ≤ (2 / 5) * ξ ^ (1 / 4 : ℝ) := by
  have hξ1 : (1 : ℝ) ≤ ξ := by linarith
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hstep : ξ ^ (1 / (k : ℝ) - 1 / 4 : ℝ) ≤ (2 / 5 : ℝ) := by
    have hexp : (1 : ℝ) / (k : ℝ) - 1 / 4 ≤ -(1 / 8 : ℝ) := by
      have hle : (1 : ℝ) / (k : ℝ) ≤ 1 / 8 :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) (by exact_mod_cast h8)
      linarith
    calc ξ ^ (1 / (k : ℝ) - 1 / 4 : ℝ) ≤ ξ ^ (-(1 / 8) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hξ1 hexp
      _ = (ξ ^ (1 / 8 : ℝ))⁻¹ := Real.rpow_neg hξ0.le _
      _ ≤ ((5 / 2 : ℝ))⁻¹ :=
          (inv_le_inv₀ (Real.rpow_pos_of_pos hξ0 _) (by norm_num)).mpr (rpow_eighth_ge hξ)
      _ = 2 / 5 := by norm_num
  calc ξ ^ (1 / (k : ℝ)) = ξ ^ (1 / 4 : ℝ) * ξ ^ (1 / (k : ℝ) - 1 / 4 : ℝ) := by
        rw [← Real.rpow_add hξ0, show (1 : ℝ) / 4 + (1 / (k : ℝ) - 1 / 4) = 1 / (k : ℝ) by ring]
    _ ≤ ξ ^ (1 / 4 : ℝ) * (2 / 5) :=
        mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hξ0.le _)
    _ = (2 / 5) * ξ ^ (1 / 4 : ℝ) := by ring

private lemma root_le_tenth {ξ : ℝ} (hξ : 1530 ≤ ξ) {k : ℕ} (h12 : 12 ≤ k) (h14 : k ≤ 14) :
    ξ ^ (1 / (k : ℝ)) ≤ (3 / 10) * ξ ^ (1 / 4 : ℝ) := by
  have hξ1 : (1 : ℝ) ≤ ξ := by linarith
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hstep : ξ ^ (1 / (k : ℝ) - 1 / 4 : ℝ) ≤ (3 / 10 : ℝ) := by
    have hexp : (1 : ℝ) / (k : ℝ) - 1 / 4 ≤ -(1 / 6 : ℝ) := by
      have hle : (1 : ℝ) / (k : ℝ) ≤ 1 / 12 :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 12) (by exact_mod_cast h12)
      linarith
    have hsix : (10 / 3 : ℝ) ≤ ξ ^ (1 / 6 : ℝ) := rpow_sixth_ge hξ
    calc ξ ^ (1 / (k : ℝ) - 1 / 4 : ℝ) ≤ ξ ^ (-(1 / 6) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hξ1 hexp
      _ = (ξ ^ (1 / 6 : ℝ))⁻¹ := Real.rpow_neg hξ0.le _
      _ ≤ ((10 / 3 : ℝ))⁻¹ :=
          (inv_le_inv₀ (Real.rpow_pos_of_pos hξ0 _) (by norm_num)).mpr hsix
      _ = 3 / 10 := by norm_num
  calc ξ ^ (1 / (k : ℝ)) = ξ ^ (1 / 4 : ℝ) * ξ ^ (1 / (k : ℝ) - 1 / 4 : ℝ) := by
        rw [← Real.rpow_add hξ0, show (1 : ℝ) / 4 + (1 / (k : ℝ) - 1 / 4) = 1 / (k : ℝ) by ring]
    _ ≤ ξ ^ (1 / 4 : ℝ) * (3 / 10) :=
        mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hξ0.le _)
    _ = (3 / 10) * ξ ^ (1 / 4 : ℝ) := by ring

private lemma mid_sum_bound (ξ : ℝ) (hξ : 1530 ≤ ξ) (K : ℕ) :
    (∑ k ∈ Finset.Icc (3:ℕ) (min K 14), ξ ^ (1 / (k : ℝ))) ≤ ξ ^ (1 / 3 : ℝ) + 6.5 * ξ ^ (1 / 4 : ℝ) := by
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have h1 : (∑ k ∈ Finset.Icc (3:ℕ) (min K 14), ξ ^ (1 / (k : ℝ)))
      ≤ ∑ k ∈ Finset.Icc (3:ℕ) 14, ξ ^ (1 / (k : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      omega
    · intro k _ _
      exact Real.rpow_nonneg hξ0.le _
  have h2 : (∑ k ∈ Finset.Icc (3:ℕ) 14, ξ ^ (1 / (k : ℝ)))
      = ξ ^ (1 / 3 : ℝ) + ∑ k ∈ Finset.Icc (4:ℕ) 14, ξ ^ (1 / (k : ℝ)) := by
    rw [show Finset.Icc (3:ℕ) 14 = insert (3:ℕ) (Finset.Icc (4:ℕ) 14) by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp)]
    norm_num
  have h3 : (∑ k ∈ Finset.Icc (4:ℕ) 14, ξ ^ (1 / (k : ℝ))) ≤ 6.5 * ξ ^ (1 / 4 : ℝ) := by
    rw [show Finset.Icc (4:ℕ) 14 = Finset.Ico (4:ℕ) 15 by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
      Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ j ∈ Finset.range 11,
        ξ ^ (1 / (((4 + j : ℕ)) : ℝ)) ≤
          (if j ≤ 3 then (1 : ℝ) else if j ≤ 7 then 2 / 5 else 3 / 10) * ξ ^ (1 / 4 : ℝ) := by
      intro j hj
      rw [Finset.mem_range] at hj
      by_cases h3' : j ≤ 3
      · rw [if_pos h3']
        have h := root_le_quarter hξ (k := 4 + j) (by omega) (by omega)
        simpa using h
      · rw [if_neg h3']
        by_cases h7' : j ≤ 7
        · rw [if_pos h7']
          have h := root_le_fifth hξ (k := 4 + j) (by omega) (by omega)
          simpa using h
        · rw [if_neg h7']
          have h := root_le_tenth hξ (k := 4 + j) (by omega) (by omega)
          simpa using h
    calc (∑ j ∈ Finset.range (15 - 4), ξ ^ (1 / (((4 + j : ℕ)) : ℝ)))
        ≤ ∑ j ∈ Finset.range 11,
            (if j ≤ 3 then (1 : ℝ) else if j ≤ 7 then 2 / 5 else 3 / 10) * ξ ^ (1 / 4 : ℝ) := by
          have : (15 - 4 : ℕ) = 11 := by norm_num
          rw [this]
          exact Finset.sum_le_sum hterm
      _ = (∑ j ∈ Finset.range 11,
            (if j ≤ 3 then (1 : ℝ) else if j ≤ 7 then 2 / 5 else 3 / 10)) * ξ ^ (1 / 4 : ℝ) := by
          rw [Finset.sum_mul]
      _ = 6.5 * ξ ^ (1 / 4 : ℝ) := by
          congr 1
          norm_num [Finset.sum_range_succ]
  linarith [h1, h2 ▸ h1]

private lemma caDelta_mid (ξ : ℝ) (hξ : 1530 ≤ ξ) (K : ℕ) :
    (∑ k ∈ Finset.Icc (3:ℕ) (min K 14), caU ((1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ))))
      ≤ 1.71 * ξ ^ (1 / 3 : ℝ) + 11.1 * ξ ^ (1 / 4 : ℝ) := by
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have hterm : ∀ k ∈ Finset.Icc (3:ℕ) (min K 14),
      caU ((1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ))) ≤ 1.703 * ξ ^ (1 / (k : ℝ)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨hk3, hkmin⟩ := hk
    have hk14 : k ≤ 14 := by omega
    have hkid : k ∈ Finset.Icc (3:ℕ) 14 := by simp only [Finset.mem_Icc]; exact ⟨hk3, hk14⟩
    have hsplit : (1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ))
        = (1.23 * (k : ℝ)) ^ (1 / (k : ℝ)) * ξ ^ (1 / (k : ℝ)) := by
      rw [show (1.23 * (k : ℝ) * ξ) = (1.23 * (k : ℝ)) * ξ by ring,
        Real.mul_rpow (by positivity : (0 : ℝ) ≤ 1.23 * (k : ℝ)) (le_of_lt hξ0)]
    have hU := caU_le_10987 ((1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ)))
      (Real.rpow_nonneg (by positivity) _)
    have hak := ak_le_155 k hkid
    have hξnn : (0 : ℝ) ≤ ξ ^ (1 / (k : ℝ)) := Real.rpow_nonneg hξ0.le _
    have hmul : (1.23 * (k : ℝ)) ^ (1 / (k : ℝ)) * ξ ^ (1 / (k : ℝ))
        ≤ 1.55 * ξ ^ (1 / (k : ℝ)) := mul_le_mul_of_nonneg_right hak hξnn
    rw [hsplit] at hU ⊢
    nlinarith [hU, hmul, hξnn]
  calc (∑ k ∈ Finset.Icc (3:ℕ) (min K 14), caU ((1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ))))
      ≤ ∑ k ∈ Finset.Icc (3:ℕ) (min K 14), 1.703 * ξ ^ (1 / (k : ℝ)) := Finset.sum_le_sum hterm
    _ = 1.703 * ∑ k ∈ Finset.Icc (3:ℕ) (min K 14), ξ ^ (1 / (k : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ 1.703 * (ξ ^ (1 / 3 : ℝ) + 6.5 * ξ ^ (1 / 4 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left (mid_sum_bound ξ hξ K) (by norm_num)
    _ = 1.703 * ξ ^ (1 / 3 : ℝ) + 11.0695 * ξ ^ (1 / 4 : ℝ) := by ring
    _ ≤ 1.71 * ξ ^ (1 / 3 : ℝ) + 11.1 * ξ ^ (1 / 4 : ℝ) := by
        have h3 : (0 : ℝ) ≤ ξ ^ (1 / 3 : ℝ) := Real.rpow_nonneg hξ0.le _
        have h4 : (0 : ℝ) ≤ ξ ^ (1 / 4 : ℝ) := Real.rpow_nonneg hξ0.le _
        nlinarith

/-! ## the count bound and the tail -/

private lemma caL_nonneg (t : ℝ) : 0 ≤ caL t := by
  unfold caL; split_ifs <;> nlinarith

private lemma pow_bound_ge19 (n : ℕ) (hn : 19 ≤ n) :
    (15375 : ℝ) * (n : ℝ) * ((n : ℝ) - 14) ^ 3 ≤ 100 * (2 : ℝ) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hnR : (19 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hstep : ((n : ℝ) + 1) * ((n : ℝ) + 1 - 14) ^ 3 ≤ 2 * (n : ℝ) * ((n : ℝ) - 14) ^ 3 := by
        have hden : (0 : ℝ) < (n : ℝ) - 14 := by linarith
        have h1 : ((n : ℝ) + 1) ≤ (20 / 19) * (n : ℝ) := by linarith
        have h2 : ((n : ℝ) + 1 - 14) ≤ (6 / 5) * ((n : ℝ) - 14) := by linarith
        have hb1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by linarith
        have hb2 : (0 : ℝ) ≤ (6 / 5 : ℝ) * ((n : ℝ) - 14) :=
          mul_nonneg (by norm_num) (le_of_lt hden)
        have hb3 : (0 : ℝ) ≤ (20 / 19 : ℝ) * (n : ℝ) :=
          mul_nonneg (by norm_num) (by linarith)
        have h3 : ((n : ℝ) + 1 - 14) ^ 3 ≤ ((6 / 5) * ((n : ℝ) - 14)) ^ 3 :=
          pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1 - 14) h2 3
        have h4 : ((n : ℝ) + 1) * ((n : ℝ) + 1 - 14) ^ 3
            ≤ ((20 / 19) * (n : ℝ)) * (((6 / 5) * ((n : ℝ) - 14)) ^ 3) :=
          mul_le_mul h1 h3 (pow_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1 - 14) 3) hb3
        have h5 : ((20 / 19 : ℝ) * (n : ℝ)) * (((6 / 5) * ((n : ℝ) - 14)) ^ 3)
            = ((20 / 19) * ((6 / 5) ^ 3)) * ((n : ℝ) * ((n : ℝ) - 14) ^ 3) := by ring
        have h6 : ((20 / 19 : ℝ) * (6 / 5) ^ 3) ≤ 2 := by norm_num
        have h7 : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 14) ^ 3 :=
          mul_nonneg (by linarith) (pow_nonneg (le_of_lt hden) 3)
        rw [h5] at h4
        linarith [h4, mul_le_mul_of_nonneg_right h6 h7]
      push_cast
      calc (15375 : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 1 - 14) ^ 3
          = (15375 : ℝ) * (((n : ℝ) + 1) * ((n : ℝ) + 1 - 14) ^ 3) := by ring
        _ ≤ (15375 : ℝ) * (2 * (n : ℝ) * ((n : ℝ) - 14) ^ 3) :=
            mul_le_mul_of_nonneg_left hstep (by norm_num)
        _ = 2 * ((15375 : ℝ) * (n : ℝ) * ((n : ℝ) - 14) ^ 3) := by ring
        _ ≤ 2 * (100 * (2 : ℝ) ^ n) := by linarith [ih]
        _ = 100 * (2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

private lemma pow_bound (k : ℕ) (hk : 15 ≤ k) :
    (15375 : ℝ) * (k : ℝ) * ((k : ℝ) - 14) ^ 3 ≤ 100 * (2 : ℝ) ^ k := by
  rcases Nat.lt_or_ge k 19 with h | h
  · interval_cases k <;> norm_num
  · exact pow_bound_ge19 k h

private lemma caDelta_tail (ξ : ℝ) (hξ : 1530 ≤ ξ) (K : ℕ) :
    (∑ k ∈ Finset.Icc (15 : ℕ) K, caU ((1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ))))
      ≤ 0.275 * ξ ^ (2 / 5 : ℝ) := by
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have hξ1 : (1 : ℝ) ≤ ξ := by linarith
  have hcard : (((Finset.Icc (15 : ℕ) K).filter
      (fun k : ℕ => (2 : ℝ) ^ k ≤ 1.23 * (k : ℝ) * ξ)).card : ℝ) ≤ ξ ^ (1 / 3 : ℝ) / 5 := by
    have hsub : (Finset.Icc (15 : ℕ) K).filter (fun k : ℕ => (2 : ℝ) ^ k ≤ 1.23 * (k : ℝ) * ξ)
        ⊆ Finset.Icc (15 : ℕ) ⌊14 + ξ ^ (1 / 3 : ℝ) / 5⌋₊ := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      obtain ⟨⟨hk15, _⟩, hpow⟩ := hk
      rw [Finset.mem_Icc]
      refine ⟨hk15, ?_⟩
      apply Nat.le_floor
      have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      have hkey := pow_bound k hk15
      have h1 : (15375 : ℝ) * (k : ℝ) * ((k : ℝ) - 14) ^ 3 ≤ 123 * (k : ℝ) * ξ := by
        have h2 : (100 : ℝ) * (2 : ℝ) ^ k ≤ 100 * (1.23 * (k : ℝ) * ξ) := by linarith [hpow]
        linarith [hkey, h2]
      have h3 : ((k : ℝ) - 14) ^ 3 ≤ ξ / 125 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 125)]
        nlinarith [h1, hk0]
      have h4 : ξ / 125 = (ξ ^ (1 / 3 : ℝ) / 5) ^ 3 := by
        rw [div_pow, show (5 : ℝ) ^ 3 = 125 by norm_num,
          ← Real.rpow_natCast (ξ ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hξ0.le]
        norm_num
      have h5 : ((k : ℝ) - 14) ^ 3 ≤ (ξ ^ (1 / 3 : ℝ) / 5) ^ 3 := by rw [← h4]; exact h3
      have h6 : (0 : ℝ) ≤ ξ ^ (1 / 3 : ℝ) / 5 := by positivity
      have h7 : (0 : ℝ) ≤ (k : ℝ) - 14 := by
        have : (14 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 14 ≤ k)
        linarith
      have h8 : (k : ℝ) - 14 ≤ ξ ^ (1 / 3 : ℝ) / 5 :=
        (pow_le_pow_iff_left₀ h7 h6 (by norm_num : (3 : ℕ) ≠ 0)).mp h5
      linarith
    have hcardN : ((Finset.Icc (15 : ℕ) K).filter
        (fun k : ℕ => (2 : ℝ) ^ k ≤ 1.23 * (k : ℝ) * ξ)).card
        ≤ ⌊14 + ξ ^ (1 / 3 : ℝ) / 5⌋₊ - 14 := by
      calc ((Finset.Icc (15 : ℕ) K).filter (fun k : ℕ => (2 : ℝ) ^ k ≤ 1.23 * (k : ℝ) * ξ)).card
          ≤ (Finset.Icc (15 : ℕ) ⌊14 + ξ ^ (1 / 3 : ℝ) / 5⌋₊).card := Finset.card_le_card hsub
        _ = ⌊14 + ξ ^ (1 / 3 : ℝ) / 5⌋₊ - 14 := by
            rw [Nat.card_Icc]
            omega
    have hcast : ((⌊14 + ξ ^ (1 / 3 : ℝ) / 5⌋₊ - 14 : ℕ) : ℝ) ≤ ξ ^ (1 / 3 : ℝ) / 5 := by
      have hx : (0 : ℝ) ≤ ξ ^ (1 / 3 : ℝ) / 5 := by positivity
      rw [Nat.cast_sub (Nat.le_floor (by linarith : (14 : ℝ) ≤ 14 + ξ ^ (1 / 3 : ℝ) / 5))]
      have hfl := Nat.floor_le (by linarith : (0 : ℝ) ≤ 14 + ξ ^ (1 / 3 : ℝ) / 5)
      push_cast
      linarith
    exact le_trans (by exact_mod_cast hcardN) hcast
  have hterm : ∀ k ∈ Finset.Icc (15 : ℕ) K,
      caU ((1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ)))
        ≤ (if (2 : ℝ) ^ k ≤ 1.23 * (k : ℝ) * ξ then 1.375 * ξ ^ (1 / 15 : ℝ) else 0) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    obtain ⟨hk15, _⟩ := hk
    by_cases hcond : (2 : ℝ) ^ k ≤ 1.23 * (k : ℝ) * ξ
    · rw [if_pos hcond]
      have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      have hsplit : (1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ))
          = (1.23 * (k : ℝ)) ^ (1 / (k : ℝ)) * ξ ^ (1 / (k : ℝ)) := by
        rw [show (1.23 * (k : ℝ) * ξ) = (1.23 * (k : ℝ)) * ξ by ring,
          Real.mul_rpow (by positivity : (0 : ℝ) ≤ 1.23 * (k : ℝ)) (le_of_lt hξ0)]
      have hU := caU_le_10987 ((1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ)))
        (Real.rpow_nonneg (by positivity) _)
      have hak := ak_le_125 k hk15
      have hξnn : (0 : ℝ) ≤ ξ ^ (1 / (k : ℝ)) := Real.rpow_nonneg hξ0.le _
      have hroot : ξ ^ (1 / (k : ℝ)) ≤ ξ ^ (1 / 15 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hξ1
        exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 15) (by exact_mod_cast hk15)
      have hmul : (1.23 * (k : ℝ)) ^ (1 / (k : ℝ)) * ξ ^ (1 / (k : ℝ))
          ≤ 1.25 * ξ ^ (1 / 15 : ℝ) :=
        le_trans (mul_le_mul_of_nonneg_right hak hξnn)
          (mul_le_mul_of_nonneg_left hroot (by norm_num))
      rw [hsplit] at hU ⊢
      nlinarith [hU, hmul]
    · rw [if_neg hcond]
      have hlt : (1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ)) < 2 := by
        have hpow : (1.23 * (k : ℝ) * ξ) < (2 : ℝ) ^ k := lt_of_not_ge hcond
        calc (1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ))
            < ((2 : ℝ) ^ k) ^ (1 / (k : ℝ)) :=
              Real.rpow_lt_rpow (by positivity) hpow (by positivity)
          _ = 2 := by
              have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
              rw [← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
                mul_one_div, div_self hkne, Real.rpow_one]
      rw [caU_eq_zero' hlt]
  calc (∑ k ∈ Finset.Icc (15 : ℕ) K, caU ((1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ))))
      ≤ ∑ k ∈ Finset.Icc (15 : ℕ) K,
          (if (2 : ℝ) ^ k ≤ 1.23 * (k : ℝ) * ξ then 1.375 * ξ ^ (1 / 15 : ℝ) else 0) :=
        Finset.sum_le_sum hterm
    _ = 1.375 * ξ ^ (1 / 15 : ℝ)
          * (((Finset.Icc (15 : ℕ) K).filter (fun k : ℕ => (2 : ℝ) ^ k ≤ 1.23 * (k : ℝ) * ξ)).card : ℝ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ 1.375 * ξ ^ (1 / 15 : ℝ) * (ξ ^ (1 / 3 : ℝ) / 5) := by
        have h2 : (((Finset.Icc (15 : ℕ) K).filter
            (fun k : ℕ => (2 : ℝ) ^ k ≤ 1.23 * (k : ℝ) * ξ)).card : ℝ) ≤ ξ ^ (1 / 3 : ℝ) / 5 := hcard
        have h1 : (0 : ℝ) ≤ 1.375 * ξ ^ (1 / 15 : ℝ) := by positivity
        nlinarith
    _ = 0.275 * ξ ^ (2 / 5 : ℝ) := by
        rw [show (1.375 : ℝ) * ξ ^ (1 / 15 : ℝ) * (ξ ^ (1 / 3 : ℝ) / 5)
              = (1.375 / 5) * (ξ ^ (1 / 15 : ℝ) * ξ ^ (1 / 3 : ℝ)) by ring,
          ← Real.rpow_add hξ0, show (1 / 15 : ℝ) + 1 / 3 = 2 / 5 by norm_num]
        norm_num

/-! ## final arithmetic and assembly -/

private lemma rpow_third_le {ξ : ℝ} (hξ : 1530 ≤ ξ) :
    ξ ^ (1 / 3 : ℝ) ≤ 0.295 * Real.sqrt ξ := by
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have hroot : (3.39 : ℝ) ≤ ξ ^ (1 / 6 : ℝ) := by
    have h1 : (3.39 : ℝ) ≤ (1530 : ℝ) ^ (1 / 6 : ℝ) := by
      have h2 : ((3.39 : ℝ)) ^ (6 : ℝ) ≤ ((1530 : ℝ) ^ (1 / 6 : ℝ)) ^ (6 : ℝ) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1530), show (1 / 6 : ℝ) * 6 = 1 by norm_num,
          Real.rpow_one]
        norm_num
      exact (Real.rpow_le_rpow_iff (by norm_num) (by positivity) (by norm_num : (0 : ℝ) < 6)).mp h2
    exact le_trans h1 (Real.rpow_le_rpow (by norm_num) hξ (by norm_num))
  have h6 : ξ ^ (-(1 / 6) : ℝ) ≤ 0.295 := by
    rw [Real.rpow_neg hξ0.le]
    calc (ξ ^ (1 / 6 : ℝ))⁻¹ ≤ ((3.39 : ℝ))⁻¹ :=
          (inv_le_inv₀ (Real.rpow_pos_of_pos hξ0 _) (by norm_num)).mpr hroot
      _ ≤ 0.295 := by norm_num
  calc ξ ^ (1 / 3 : ℝ) = Real.sqrt ξ * ξ ^ (-(1 / 6) : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hξ0, show (1 / 2 : ℝ) + (-(1 / 6)) = 1 / 3 by norm_num]
    _ ≤ Real.sqrt ξ * 0.295 := mul_le_mul_of_nonneg_left h6 (Real.sqrt_nonneg ξ)
    _ = 0.295 * Real.sqrt ξ := by ring

private lemma rpow_quarter_le {ξ : ℝ} (hξ : 1530 ≤ ξ) :
    ξ ^ (1 / 4 : ℝ) ≤ 0.16 * Real.sqrt ξ := by
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have hroot : (6.25 : ℝ) ≤ ξ ^ (1 / 4 : ℝ) := by
    have h1 : (6.25 : ℝ) ≤ (1530 : ℝ) ^ (1 / 4 : ℝ) := by
      have h2 : ((6.25 : ℝ)) ^ (4 : ℝ) ≤ ((1530 : ℝ) ^ (1 / 4 : ℝ)) ^ (4 : ℝ) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1530), show (1 / 4 : ℝ) * 4 = 1 by norm_num,
          Real.rpow_one]
        norm_num
      exact (Real.rpow_le_rpow_iff (by norm_num) (by positivity) (by norm_num : (0 : ℝ) < 4)).mp h2
    exact le_trans h1 (Real.rpow_le_rpow (by norm_num) hξ (by norm_num))
  have h4 : ξ ^ (-(1 / 4) : ℝ) ≤ 0.16 := by
    rw [Real.rpow_neg hξ0.le]
    calc (ξ ^ (1 / 4 : ℝ))⁻¹ ≤ ((6.25 : ℝ))⁻¹ :=
          (inv_le_inv₀ (Real.rpow_pos_of_pos hξ0 _) (by norm_num)).mpr hroot
      _ ≤ 0.16 := by norm_num
  calc ξ ^ (1 / 4 : ℝ) = Real.sqrt ξ * ξ ^ (-(1 / 4) : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hξ0, show (1 / 2 : ℝ) + (-(1 / 4)) = 1 / 4 by norm_num]
    _ ≤ Real.sqrt ξ * 0.16 := mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg ξ)
    _ = 0.16 * Real.sqrt ξ := by ring

private lemma rpow_twofifth_le {ξ : ℝ} (hξ : 1530 ≤ ξ) :
    ξ ^ (2 / 5 : ℝ) ≤ 0.4855 * Real.sqrt ξ := by
  have hξ0 : (0 : ℝ) < ξ := by linarith
  have hroot : (2.06 : ℝ) ≤ ξ ^ (1 / 10 : ℝ) := by
    have h1 : (2.06 : ℝ) ≤ (1530 : ℝ) ^ (1 / 10 : ℝ) := by
      have h2 : ((2.06 : ℝ)) ^ (10 : ℝ) ≤ ((1530 : ℝ) ^ (1 / 10 : ℝ)) ^ (10 : ℝ) := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1530), show (1 / 10 : ℝ) * 10 = 1 by norm_num,
          Real.rpow_one]
        norm_num
      exact (Real.rpow_le_rpow_iff (by norm_num) (by positivity) (by norm_num : (0 : ℝ) < 10)).mp h2
    exact le_trans h1 (Real.rpow_le_rpow (by norm_num) hξ (by norm_num))
  have h10 : ξ ^ (-(1 / 10) : ℝ) ≤ 0.4855 := by
    rw [Real.rpow_neg hξ0.le]
    calc (ξ ^ (1 / 10 : ℝ))⁻¹ ≤ ((2.06 : ℝ))⁻¹ :=
          (inv_le_inv₀ (Real.rpow_pos_of_pos hξ0 _) (by norm_num)).mpr hroot
      _ ≤ 0.4855 := by norm_num
  calc ξ ^ (2 / 5 : ℝ) = Real.sqrt ξ * ξ ^ (-(1 / 10) : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hξ0, show (1 / 2 : ℝ) + (-(1 / 10)) = 2 / 5 by norm_num]
    _ ≤ Real.sqrt ξ * 0.4855 := mul_le_mul_of_nonneg_left h10 (Real.sqrt_nonneg ξ)
    _ = 0.4855 * Real.sqrt ξ := by ring

private lemma final_arith (ξ : ℝ) (hξ : 1530 ≤ ξ) :
    1.03 * Real.sqrt ξ + (1.71 * ξ ^ (1 / 3 : ℝ) + 11.1 * ξ ^ (1 / 4 : ℝ))
      + 0.275 * ξ ^ (2 / 5 : ℝ) ≤ 4 * Real.sqrt ξ := by
  have h3 := rpow_third_le hξ
  have h4 := rpow_quarter_le hξ
  have h5 := rpow_twofifth_le hξ
  have hs : (0 : ℝ) ≤ Real.sqrt ξ := Real.sqrt_nonneg ξ
  nlinarith [h3, h4, h5, hs]

/-- The pure numeric bound on the truncated `Δ`-sum: `∑_{k=2}^{K}` of the step-function
terms is at most `4 √ξ`. -/
private theorem caDelta_aux (ξ : ℝ) (hξ : 1530 ≤ ξ) (K : ℕ) :
    (∑ k ∈ Finset.Icc 2 K,
      (caU ((1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ)))
        - caL (ξ ^ (1 / (k : ℝ)))))
      ≤ 4 * Real.sqrt ξ := by
  have hξ0 : (0 : ℝ) < ξ := by linarith
  rcases lt_or_ge K 2 with hK | hK
  · have hempty : Finset.Icc 2 K = ∅ := by
      rw [Finset.Icc_eq_empty_iff]; omega
    rw [hempty]
    simp only [Finset.sum_empty]
    nlinarith [Real.sqrt_nonneg ξ]
  · have hsplit2 : Finset.Icc 2 K = insert 2 (Finset.Icc 3 K) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hsplit3 : Finset.Icc 3 K = Finset.Icc 3 (min K 14) ∪ Finset.Icc 15 K := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc 3 (min K 14)) (Finset.Icc 15 K) := by
      rw [Finset.disjoint_left]
      intro k hk1 hk2
      simp only [Finset.mem_Icc] at hk1 hk2
      omega
    rw [hsplit2, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), hsplit3,
      Finset.sum_union hdisj]
    have hT2 := T2_bound ξ hξ
    have hmid0 := caDelta_mid ξ hξ K
    have htail0 := caDelta_tail ξ hξ K
    have hdrop1 : (∑ k ∈ Finset.Icc 3 (min K 14),
        (caU ((1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ))) - caL (ξ ^ (1 / (k : ℝ)))))
        ≤ ∑ k ∈ Finset.Icc 3 (min K 14), caU ((1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ))) :=
      Finset.sum_le_sum (fun k _ => sub_le_self _ (caL_nonneg _))
    have hdrop2 : (∑ k ∈ Finset.Icc 15 K,
        (caU ((1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ))) - caL (ξ ^ (1 / (k : ℝ)))))
        ≤ ∑ k ∈ Finset.Icc 15 K, caU ((1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ))) :=
      Finset.sum_le_sum (fun k _ => sub_le_self _ (caL_nonneg _))
    have hfin := final_arith ξ hξ
    linarith [hT2, hmid0, htail0, hdrop1, hdrop2, hfin]

/-- `θ x ≤ log 3 · x` for `x ≥ 0` (the crude Chebyshev bound, at every real argument). -/
private lemma theta_le_log3_real (x : ℝ) (hx : 0 ≤ x) : Chebyshev.theta x ≤ Real.log 3 * x := by
  rw [Commons.NumberTheory.Chebyshev.theta_eq_theta_floor x]
  have h := Commons.NumberTheory.Chebyshev.theta_le_log3_mul ⌊x⌋₊
  have hfl : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx
  calc Chebyshev.theta ((⌊x⌋₊ : ℕ) : ℝ) ≤ Real.log 3 * ((⌊x⌋₊ : ℕ) : ℝ) := h
    _ ≤ Real.log 3 * x := mul_le_mul_of_nonneg_left hfl (Real.log_nonneg (by norm_num))

theorem log_caNumber_sub_psi_bounds (ε : ℝ) (hε : 0 < ε) (hξ : 1530 ≤ (Work.RHPlan.caXi ε : ℝ))
    (hS1 : ∀ p : ℕ, Nat.Prime p → p ≤ Work.RHPlan.caXi ε →
      Nat.log p (Work.RHPlan.caXi ε) ≤ ⌊Work.RHPlan.caMu p ε⌋₊) :
    0 ≤ Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ) - Chebyshev.psi (Work.RHPlan.caXi ε : ℝ) ∧
    Real.log ((Work.RHPlan.caNumber ε : ℕ) : ℝ) - Chebyshev.psi (Work.RHPlan.caXi ε : ℝ)
      ≤ 4 * Real.sqrt (Work.RHPlan.caXi ε : ℝ) := by
  refine ⟨?_, ?_⟩
  · simpa using Work.RHContract.A.ca_delta_nonneg ε hε hξ
  · set ξ : ℝ := (Work.RHPlan.caXi ε : ℝ) with hξdef
    have hξ1530 : 1530 ≤ ξ := by rw [hξdef]; exact hξ
    have hξ1 : 1 ≤ ξ := by linarith
    have hK1 : 1 ≤ Work.RHContract.A.caK ε := by
      unfold Work.RHContract.A.caK; omega
    have hlog : Real.log (Work.RHPlan.caNumber ε : ℝ)
        = ∑ k ∈ Finset.Icc 1 (Work.RHContract.A.caK ε),
            Chebyshev.theta ((Work.RHContract.A.caLevel ε k : ℝ)) := by
      have h := Commons.NumberTheory.Robin.caLogN_eq_sum_theta ε hε
      unfold Work.RHContract.A.caLevel Work.RHContract.A.caK Work.RHPlan.caNumber at *
      simp only [Work.RHPlan.caMu] at h ⊢
      exact h
    have hlev1 : Work.RHContract.A.caLevel ε 1 = Work.RHPlan.caXi ε := by
      unfold Work.RHContract.A.caLevel Work.RHContract.A.caK Work.RHPlan.caXi
        Work.RHPlan.caSupport Work.RHPlan.caMu
      simp
    have hsplit : (∑ k ∈ Finset.Icc 1 (Work.RHContract.A.caK ε),
          (Chebyshev.theta ((Work.RHContract.A.caLevel ε k : ℝ))
            - Chebyshev.theta (ξ ^ (1 / (k : ℝ)))))
        = (Chebyshev.theta ((Work.RHContract.A.caLevel ε 1 : ℝ))
            - Chebyshev.theta (ξ ^ (1 / ((1 : ℕ) : ℝ))))
          + ∑ k ∈ Finset.Icc 2 (Work.RHContract.A.caK ε),
              (Chebyshev.theta ((Work.RHContract.A.caLevel ε k : ℝ))
                - Chebyshev.theta (ξ ^ (1 / (k : ℝ)))) := by
      have hIcc : Finset.Icc 1 (Work.RHContract.A.caK ε)
          = insert 1 (Finset.Icc 2 (Work.RHContract.A.caK ε)) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hIcc, Finset.sum_insert (by simp [Finset.mem_Icc])]
    have hk1val : Chebyshev.theta ((Work.RHContract.A.caLevel ε 1 : ℝ))
        - Chebyshev.theta (ξ ^ (1 / ((1 : ℕ) : ℝ))) = 0 := by
      have h1 : (Work.RHContract.A.caLevel ε 1 : ℝ) = ξ := by rw [hlev1, hξdef]
      have h2 : ξ ^ (1 / ((1 : ℕ) : ℝ)) = ξ := by
        rw [show (1 / ((1 : ℕ) : ℝ)) = (1 : ℝ) by norm_num, Real.rpow_one]
      rw [h1, h2, sub_self]
    have hterm : ∀ k ∈ Finset.Icc 2 (Work.RHContract.A.caK ε),
        Chebyshev.theta ((Work.RHContract.A.caLevel ε k : ℝ))
          - Chebyshev.theta (ξ ^ (1 / (k : ℝ)))
        ≤ Work.RHContract.A.caU ((1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ)))
          - Work.RHContract.A.caL (ξ ^ (1 / (k : ℝ))) := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      obtain ⟨hk2, _⟩ := hk
      have hcle : (Work.RHContract.A.caLevel ε k : ℝ)
          ≤ (1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ)) := by
        simpa only [hξdef] using Work.RHContract.A.caLevel_le ε hε hξ k hk2
      have hz_nonneg : 0 ≤ (1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ)) :=
        Real.rpow_nonneg (by positivity) _
      have hupper : Chebyshev.theta ((Work.RHContract.A.caLevel ε k : ℝ))
          ≤ Work.RHContract.A.caU ((1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ))) := by
        have hm : Chebyshev.theta ((Work.RHContract.A.caLevel ε k : ℝ))
            ≤ Chebyshev.theta ((1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ))) :=
          Chebyshev.theta_mono hcle
        refine le_trans hm ?_
        unfold Work.RHContract.A.caU
        by_cases h2 : (1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ)) < 2
        · rw [if_pos h2, Chebyshev.theta_eq_zero_iff.mpr h2]
        · rw [if_neg h2]
          by_cases h3 : (1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ)) ≤ 1530
          · rw [if_pos h3]
            exact Work.RHContract.A.theta_le_self_small _ (le_of_not_gt h2) h3
          · rw [if_neg h3]
            exact theta_le_log3_real _ hz_nonneg
      have hlower : Work.RHContract.A.caL (ξ ^ (1 / (k : ℝ)))
          ≤ Chebyshev.theta (ξ ^ (1 / (k : ℝ))) := by
        set y : ℝ := ξ ^ (1 / (k : ℝ)) with hydef
        by_cases h3 : y < 3
        · have hcy : Work.RHContract.A.caL y = 0 := by
            unfold Work.RHContract.A.caL; rw [if_pos h3]
          rw [hcy]
          exact Chebyshev.theta_nonneg _
        · have hy3 : 3 ≤ y := le_of_not_gt h3
          by_cases h1530 : y < 1530
          · exact Work.RHContract.A.theta_ge_frac_small y hy3 h1530
          · have hcy : Work.RHContract.A.caL y = 0.9 * y := by
              unfold Work.RHContract.A.caL
              rw [if_neg h3, if_neg (by linarith : ¬ y < 39), if_neg h1530]
            have hcf := Commons.NumberTheory.Chebyshev.theta_lower_ninetenths y
              (le_of_not_gt h1530)
            rw [hcy]
            linarith
      linarith
    have hpsi := Work.RHContract.A.psi_ge_sum_theta ξ hξ1 (Work.RHContract.A.caK ε)
    have hmain : Real.log (Work.RHPlan.caNumber ε : ℝ) - Chebyshev.psi ξ
        ≤ ∑ k ∈ Finset.Icc 2 (Work.RHContract.A.caK ε),
            (Work.RHContract.A.caU ((1.23 * (k : ℝ) * ξ) ^ (1 / (k : ℝ)))
              - Work.RHContract.A.caL (ξ ^ (1 / (k : ℝ)))) := by
      have h1 : Real.log (Work.RHPlan.caNumber ε : ℝ) - Chebyshev.psi ξ
          ≤ (∑ k ∈ Finset.Icc 1 (Work.RHContract.A.caK ε),
                Chebyshev.theta ((Work.RHContract.A.caLevel ε k : ℝ)))
            - ∑ k ∈ Finset.Icc 1 (Work.RHContract.A.caK ε),
                Chebyshev.theta (ξ ^ (1 / (k : ℝ))) := by
        rw [hlog]
        linarith
      refine le_trans h1 ?_
      rw [← Finset.sum_sub_distrib, hsplit, hk1val, zero_add]
      exact Finset.sum_le_sum hterm
    have hnum := caDelta_aux ξ hξ1530 (Work.RHContract.A.caK ε)
    linarith [hmain, hnum]

end

end Work.RHContract.Helper
