import Mathlib
import Submission.Work.LinnikAreas.Density4.BzS3.S3InnerDefs
import Submission.Work.LinnikAreas.Density4.BzS3.S3GAuxDefs
import Submission.Work.LinnikAreas.Density4.BzBilin.sqfree_coprime_count_sigma
import Submission.Work.LinnikAreas.Density4.BzBilin.abel_weighted_difference_bound_range
import Submission.Work.LinnikAreas.Density4.BzS3.sqfree_coprime_count_main
import Submission.Work.LinnikAreas.Density4.BzBilin.sqfree_weighted_abel
import Submission.Work.ZeroDensity.Jutila.S3GSharpDefs

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section


/-! ## Elementary bounds -/

private lemma sum_inv_sqrt_le (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / Real.sqrt (m : ℝ)) ≤ 2 * Real.sqrt (M : ℝ) := by
  refine le_trans (le_of_eq ?_) (Work.Commons.Analysis.Series.sum_Icc_sqrt_div_self_le M)
  refine Finset.sum_congr rfl fun m hm => ?_
  obtain ⟨hm1, _⟩ := Finset.mem_Icc.mp hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hs : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos_of_pos hm0
  rw [div_eq_div_iff (ne_of_gt hs) (ne_of_gt hm0), one_mul, ← pow_two, Real.sq_sqrt hm0.le]

private lemma sum_inv_le_two_sqrt (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ)) ≤ 2 * Real.sqrt (M : ℝ) := by
  refine le_trans (Finset.sum_le_sum ?_) (sum_inv_sqrt_le M)
  intro m hm
  obtain ⟨hm1, _⟩ := Finset.mem_Icc.mp hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hs : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos_of_pos hm0
  rw [div_le_div_iff₀ hm0 hs, one_mul, one_mul]
  have hsq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) := by
    rw [← pow_two, Real.sq_sqrt hm0.le]
  have h1 : (1 : ℝ) ≤ Real.sqrt (m : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hm1)
  calc Real.sqrt (m : ℝ) = 1 * Real.sqrt (m : ℝ) := by ring
    _ ≤ Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) := mul_le_mul_of_nonneg_right h1 hs.le
    _ = (m : ℝ) := hsq

private lemma log_le_four_rpow {t : ℝ} (ht : 0 ≤ t) :
    Real.log t ≤ 4 * t ^ ((1 : ℝ) / 4) := by
  have h := Real.log_le_rpow_div ht (by norm_num : (0 : ℝ) < 1 / 4)
  have h4 : t ^ ((1 : ℝ) / 4) / ((1 : ℝ) / 4) = 4 * t ^ ((1 : ℝ) / 4) := by ring
  rw [h4] at h
  exact h

private lemma rpow_neg_three_quarters_le_diff {x : ℝ} (hx : 1 ≤ x) :
    x ^ (-(3 / 4) : ℝ) ≤ 4 * (x ^ ((1 : ℝ) / 4) - (x - 1) ^ ((1 : ℝ) / 4)) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have hy0 : 0 ≤ x - 1 := by linarith
  set a : ℝ := x ^ ((1 : ℝ) / 4) with ha
  set b : ℝ := (x - 1) ^ ((1 : ℝ) / 4) with hb
  have ha0 : 0 ≤ a := Real.rpow_nonneg hx0.le _
  have hb0 : 0 ≤ b := Real.rpow_nonneg hy0 _
  have hba : b ≤ a := by
    rw [ha, hb]
    exact Real.rpow_le_rpow hy0 (by linarith) (by norm_num)
  have ha4 : a ^ 4 = x := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hb4 : b ^ 4 = x - 1 := by
    rw [hb, ← Real.rpow_natCast, ← Real.rpow_mul hy0]
    norm_num
  have ha3 : a ^ 3 = x ^ ((3 : ℝ) / 4) := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have hfac : (a - b) * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) = 1 := by
    have h : (a - b) * (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) = a ^ 4 - b ^ 4 := by ring
    rw [h, ha4, hb4]; ring
  have hsum : a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 ≤ 4 * a ^ 3 := by
    nlinarith [ha0, hb0, hba, sq_nonneg a, sq_nonneg b, mul_nonneg ha0 hb0,
      mul_nonneg (sq_nonneg a) hb0, mul_nonneg ha0 (sq_nonneg b)]
  have ha3pos : 0 < a ^ 3 := by positivity
  have hSpos : 0 < a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 := by
    nlinarith [ha3pos, mul_nonneg (sq_nonneg a) hb0, mul_nonneg ha0 (sq_nonneg b),
      pow_nonneg hb0 3]
  have hdiff : a - b = 1 / (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) := by
    rw [eq_div_iff (ne_of_gt hSpos)]
    exact hfac
  have hmain : 1 ≤ 4 * (a - b) * a ^ 3 := by
    rw [hdiff]
    rw [show (4 : ℝ) * (1 / (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3)) * a ^ 3
        = 4 * a ^ 3 / (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) from by
      rw [div_eq_mul_inv]; ring]
    rw [le_div_iff₀ hSpos]
    nlinarith [hsum]
  have hgoal : x ^ (-(3 / 4) : ℝ) = 1 / a ^ 3 := by
    rw [ha3, Real.rpow_neg hx0.le, one_div]
  rw [hgoal, div_le_iff₀ ha3pos]
  exact hmain

private lemma sum_rpow_neg_three_quarters_le (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, (m : ℝ) ^ (-(3 / 4) : ℝ)) ≤ 4 * (M : ℝ) ^ ((1 : ℝ) / 4) := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have hkey := rpow_neg_three_quarters_le_diff (x := (n : ℝ) + 1)
      (by have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
    rw [show ((n : ℝ) + 1) - 1 = (n : ℝ) by ring] at hkey
    simp only [Nat.cast_add, Nat.cast_one]
    linarith [ih, hkey]

private lemma sum_inv_sqrt_mul_log_div_le (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / Real.sqrt (m : ℝ) * Real.log ((M : ℝ) / (m : ℝ)))
      ≤ 16 * Real.sqrt (M : ℝ) := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hterm : ∀ m ∈ Finset.Icc 1 M,
      (1 : ℝ) / Real.sqrt (m : ℝ) * Real.log ((M : ℝ) / (m : ℝ))
        ≤ 4 * (M : ℝ) ^ ((1 : ℝ) / 4) * (m : ℝ) ^ (-(3 / 4) : ℝ) := by
    intro m hm
    obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hlog : Real.log ((M : ℝ) / (m : ℝ)) ≤ 4 * ((M : ℝ) / (m : ℝ)) ^ ((1 : ℝ) / 4) :=
      log_le_four_rpow (t := (M : ℝ) / (m : ℝ)) (by positivity)
    have hdiv : ((M : ℝ) / (m : ℝ)) ^ ((1 : ℝ) / 4)
        = (M : ℝ) ^ ((1 : ℝ) / 4) / (m : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.div_rpow hM0.le hm0.le _
    have hs : (1 : ℝ) / Real.sqrt (m : ℝ) = (m : ℝ) ^ (-(1 / 2) : ℝ) := by
      rw [Real.sqrt_eq_rpow, one_div, Real.rpow_neg hm0.le]
    have hpow : (M : ℝ) ^ ((1 : ℝ) / 4) / (m : ℝ) ^ ((1 : ℝ) / 4)
        = (M : ℝ) ^ ((1 : ℝ) / 4) * (m : ℝ) ^ (-(1 / 4) : ℝ) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hm0.le]
    have hcomb : (m : ℝ) ^ (-(1 / 2) : ℝ) * (m : ℝ) ^ (-(1 / 4) : ℝ)
        = (m : ℝ) ^ (-(3 / 4) : ℝ) := by
      rw [← Real.rpow_add hm0]; norm_num
    calc (1 : ℝ) / Real.sqrt (m : ℝ) * Real.log ((M : ℝ) / (m : ℝ))
        ≤ (1 : ℝ) / Real.sqrt (m : ℝ) * (4 * ((M : ℝ) / (m : ℝ)) ^ ((1 : ℝ) / 4)) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 4 * (M : ℝ) ^ ((1 : ℝ) / 4)
            * ((m : ℝ) ^ (-(1 / 2) : ℝ) * (m : ℝ) ^ (-(1 / 4) : ℝ)) := by
          rw [hs, hdiv, hpow]; ring
      _ = 4 * (M : ℝ) ^ ((1 : ℝ) / 4) * (m : ℝ) ^ (-(3 / 4) : ℝ) := by rw [hcomb]
  calc (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / Real.sqrt (m : ℝ) * Real.log ((M : ℝ) / (m : ℝ)))
      ≤ ∑ m ∈ Finset.Icc 1 M, 4 * (M : ℝ) ^ ((1 : ℝ) / 4) * (m : ℝ) ^ (-(3 / 4) : ℝ) :=
        Finset.sum_le_sum hterm
    _ = 4 * (M : ℝ) ^ ((1 : ℝ) / 4) * (∑ m ∈ Finset.Icc 1 M, (m : ℝ) ^ (-(3 / 4) : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ 4 * (M : ℝ) ^ ((1 : ℝ) / 4) * (4 * (M : ℝ) ^ ((1 : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left (sum_rpow_neg_three_quarters_le M) (by positivity)
    _ = 16 * Real.sqrt (M : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        rw [show (4 : ℝ) * (M : ℝ) ^ ((1 : ℝ) / 4) * (4 * (M : ℝ) ^ ((1 : ℝ) / 4))
            = 16 * ((M : ℝ) ^ ((1 : ℝ) / 4) * (M : ℝ) ^ ((1 : ℝ) / 4)) from by ring]
        rw [← Real.rpow_add hM0]; norm_num

private lemma sum_inv_sqrt_abs_log_sub_le (M : ℕ) (γ : ℝ) :
    (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / Real.sqrt (m : ℝ) * |Real.log (m : ℝ) - γ|)
      ≤ 20 * Real.sqrt (M : ℝ) * (1 + |Real.log (M : ℝ) - γ|) := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hterm : ∀ m ∈ Finset.Icc 1 M,
      (1 : ℝ) / Real.sqrt (m : ℝ) * |Real.log (m : ℝ) - γ|
        ≤ (1 : ℝ) / Real.sqrt (m : ℝ) * Real.log ((M : ℝ) / (m : ℝ))
          + (1 : ℝ) / Real.sqrt (m : ℝ) * |Real.log (M : ℝ) - γ| := by
    intro m hm
    obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hmm : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
    have hlogdiv : Real.log (m : ℝ) - Real.log (M : ℝ) = -Real.log ((M : ℝ) / (m : ℝ)) := by
      rw [Real.log_div (ne_of_gt hM0) (ne_of_gt hm0)]; ring
    have hsplit : Real.log (m : ℝ) - γ
        = -(Real.log ((M : ℝ) / (m : ℝ))) + (Real.log (M : ℝ) - γ) := by
      rw [← hlogdiv]; ring
    have hdivnn : 0 ≤ Real.log ((M : ℝ) / (m : ℝ)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hm0]; simpa using hmm
    have h2 : |Real.log (m : ℝ) - γ|
        ≤ Real.log ((M : ℝ) / (m : ℝ)) + |Real.log (M : ℝ) - γ| := by
      calc |Real.log (m : ℝ) - γ|
          = |-(Real.log ((M : ℝ) / (m : ℝ))) + (Real.log (M : ℝ) - γ)| := by rw [hsplit]
        _ ≤ |-(Real.log ((M : ℝ) / (m : ℝ)))| + |Real.log (M : ℝ) - γ| := abs_add_le _ _
        _ = Real.log ((M : ℝ) / (m : ℝ)) + |Real.log (M : ℝ) - γ| := by
            rw [abs_neg, abs_of_nonneg hdivnn]
    calc (1 : ℝ) / Real.sqrt (m : ℝ) * |Real.log (m : ℝ) - γ|
        ≤ (1 : ℝ) / Real.sqrt (m : ℝ)
            * (Real.log ((M : ℝ) / (m : ℝ)) + |Real.log (M : ℝ) - γ|) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (1 : ℝ) / Real.sqrt (m : ℝ) * Real.log ((M : ℝ) / (m : ℝ))
          + (1 : ℝ) / Real.sqrt (m : ℝ) * |Real.log (M : ℝ) - γ| := by ring
  calc (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / Real.sqrt (m : ℝ) * |Real.log (m : ℝ) - γ|)
      ≤ ∑ m ∈ Finset.Icc 1 M, ((1 : ℝ) / Real.sqrt (m : ℝ) * Real.log ((M : ℝ) / (m : ℝ))
          + (1 : ℝ) / Real.sqrt (m : ℝ) * |Real.log (M : ℝ) - γ|) :=
        Finset.sum_le_sum hterm
    _ = (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / Real.sqrt (m : ℝ) * Real.log ((M : ℝ) / (m : ℝ)))
        + (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / Real.sqrt (m : ℝ)) * |Real.log (M : ℝ) - γ| := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ 16 * Real.sqrt (M : ℝ) + 2 * Real.sqrt (M : ℝ) * |Real.log (M : ℝ) - γ| := by
        have h1 := sum_inv_sqrt_mul_log_div_le M
        have h2 := sum_inv_sqrt_le M
        have h3 : (0 : ℝ) ≤ |Real.log (M : ℝ) - γ| := abs_nonneg _
        have h4 : (0 : ℝ) ≤ Real.sqrt (M : ℝ) := Real.sqrt_nonneg _
        nlinarith [h1, h2, h3, h4]
    _ ≤ 20 * Real.sqrt (M : ℝ) * (1 + |Real.log (M : ℝ) - γ|) := by
        have h4 : (0 : ℝ) ≤ Real.sqrt (M : ℝ) := Real.sqrt_nonneg _
        have h3 : (0 : ℝ) ≤ |Real.log (M : ℝ) - γ| := abs_nonneg _
        nlinarith [h3, h4]

private lemma sum_inv_abs_log_sub_le (M : ℕ) (γ : ℝ) :
    (∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (m : ℝ) * |Real.log (m : ℝ) - γ|)
      ≤ 20 * Real.sqrt (M : ℝ) * (1 + |Real.log (M : ℝ) - γ|) := by
  refine le_trans (Finset.sum_le_sum ?_) (sum_inv_sqrt_abs_log_sub_le M γ)
  intro m hm
  obtain ⟨hm1, _⟩ := Finset.mem_Icc.mp hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  have hs : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos_of_pos hm0
  have hle : (1 : ℝ) / (m : ℝ) ≤ (1 : ℝ) / Real.sqrt (m : ℝ) := by
    rw [div_le_div_iff₀ hm0 hs, one_mul, one_mul]
    have hsq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) := by
      rw [← pow_two, Real.sq_sqrt hm0.le]
    have h1 : (1 : ℝ) ≤ Real.sqrt (m : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hm1)
    calc Real.sqrt (m : ℝ) = 1 * Real.sqrt (m : ℝ) := by ring
      _ ≤ Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) := mul_le_mul_of_nonneg_right h1 hs.le
      _ = (m : ℝ) := hsq
  exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)

private lemma log_two_mul_add_one_sq_le (X : ℕ) (hX : 2 ≤ X) :
    (Real.log (2 * (X : ℝ)) + 1) ^ 2 ≤ 100 * Real.sqrt (X : ℝ) := by
  have h2X : (1 : ℝ) ≤ 2 * (X : ℝ) := by
    have : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    linarith
  have hlog : Real.log (2 * (X : ℝ)) ≤ 4 * (2 * (X : ℝ)) ^ ((1 : ℝ) / 4) :=
    log_le_four_rpow (by linarith)
  have hr1 : (1 : ℝ) ≤ (2 * (X : ℝ)) ^ ((1 : ℝ) / 4) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) h2X (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rwa [Real.one_rpow] at h
  have hpos : (0 : ℝ) ≤ Real.log (2 * (X : ℝ)) + 1 := by
    have : 0 ≤ Real.log (2 * (X : ℝ)) := Real.log_nonneg h2X
    linarith
  have hsum : Real.log (2 * (X : ℝ)) + 1 ≤ 5 * (2 * (X : ℝ)) ^ ((1 : ℝ) / 4) := by linarith
  have hsq : (Real.log (2 * (X : ℝ)) + 1) ^ 2
      ≤ (5 * (2 * (X : ℝ)) ^ ((1 : ℝ) / 4)) ^ 2 := by
    have hmm := mul_self_le_mul_self hpos hsum
    calc (Real.log (2 * (X : ℝ)) + 1) ^ 2
        = (Real.log (2 * (X : ℝ)) + 1) * (Real.log (2 * (X : ℝ)) + 1) := by ring
      _ ≤ (5 * (2 * (X : ℝ)) ^ ((1 : ℝ) / 4)) * (5 * (2 * (X : ℝ)) ^ ((1 : ℝ) / 4)) := hmm
      _ = (5 * (2 * (X : ℝ)) ^ ((1 : ℝ) / 4)) ^ 2 := by ring
  have hrhs : (5 * (2 * (X : ℝ)) ^ ((1 : ℝ) / 4)) ^ 2
      = 25 * Real.sqrt (2 * (X : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    rw [show (5 * (2 * (X : ℝ)) ^ ((1 : ℝ) / 4)) ^ 2
        = 25 * ((2 * (X : ℝ)) ^ ((1 : ℝ) / 4)) ^ 2 from by ring,
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 * (X : ℝ))]
    norm_num
  rw [hrhs] at hsq
  have hsqrt2 : Real.sqrt (2 * (X : ℝ)) ≤ 2 * Real.sqrt (X : ℝ) := by
    rw [show (2 : ℝ) * (X : ℝ) = 2 * (X : ℝ) from rfl, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hle : Real.sqrt 2 ≤ 2 := by nlinarith [h2, Real.sqrt_nonneg 2]
    exact mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg _)
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt (X : ℝ) := Real.sqrt_nonneg _
  linarith [hsq, hsqrt2, hsqrtnn]

/-! ## Pointwise bounds for the Abel weight -/

private lemma log_two_mul_sub_abs_bound (X : ℕ) (α : ℝ) :
    |Real.log (X : ℝ) - α| ≤ 2 * (1 + |Real.log (2 * (X : ℝ)) - α|) := by
  by_cases hX : X = 0
  · subst hX
    simp only [Nat.cast_zero, mul_zero, Real.log_zero, zero_sub, abs_neg]
    linarith [abs_nonneg α]
  have hX0 : (0 : ℝ) < (X : ℝ) := by positivity
  have hlog : Real.log (2 * (X : ℝ)) = Real.log 2 + Real.log (X : ℝ) :=
    Real.log_mul (by norm_num) (ne_of_gt hX0)
  have hlog2nn : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hsplit : Real.log (X : ℝ) - α
      = -(Real.log 2) + (Real.log (2 * (X : ℝ)) - α) := by rw [hlog]; ring
  calc |Real.log (X : ℝ) - α| = |-(Real.log 2) + (Real.log (2 * (X : ℝ)) - α)| := by rw [hsplit]
    _ ≤ |-(Real.log 2)| + |Real.log (2 * (X : ℝ)) - α| := abs_add_le _ _
    _ = Real.log 2 + |Real.log (2 * (X : ℝ)) - α| := by rw [abs_neg, abs_of_nonneg hlog2nn]
    _ ≤ 2 * (1 + |Real.log (2 * (X : ℝ)) - α|) := by
        linarith [abs_nonneg (Real.log (2 * (X : ℝ)) - α)]

private lemma alpha_add_one_le (X : ℕ) (α : ℝ) :
    α + 1 ≤ (Real.log (2 * (X : ℝ)) + 1) * (1 + |Real.log (2 * (X : ℝ)) - α|) := by
  have hA : (0 : ℝ) ≤ |Real.log (2 * (X : ℝ)) - α| := abs_nonneg _
  have h1 : α ≤ Real.log (2 * (X : ℝ)) + |Real.log (2 * (X : ℝ)) - α| := by
    linarith [neg_le_abs (Real.log (2 * (X : ℝ)) - α)]
  calc α + 1 ≤ (Real.log (2 * (X : ℝ)) + |Real.log (2 * (X : ℝ)) - α|) + 1 := by linarith
    _ = (Real.log (2 * (X : ℝ)) + 1) + |Real.log (2 * (X : ℝ)) - α| := by ring
    _ ≤ (Real.log (2 * (X : ℝ)) + 1) * (1 + |Real.log (2 * (X : ℝ)) - α|) := by
        rcases Nat.eq_zero_or_pos X with h | h
        · subst h
          simp only [Nat.cast_zero, mul_zero, Real.log_zero, add_zero, one_mul]
          linarith
        · have hc1 : (1 : ℝ) ≤ Real.log (2 * (X : ℝ)) + 1 := by
            have h2X : (1 : ℝ) ≤ 2 * (X : ℝ) := by
              have : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast h
              linarith
            have : (0 : ℝ) ≤ Real.log (2 * (X : ℝ)) := Real.log_nonneg h2X
            linarith
          nlinarith [hA, hc1]

private lemma wfun_abs_le (X : ℕ) (α β : ℝ) :
    |LinnikAreas.Density4.BzS3.wfun α β X| ≤
      4 * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|) := by
  have h1 := log_two_mul_sub_abs_bound X α
  have h2 := log_two_mul_sub_abs_bound X β
  rw [LinnikAreas.Density4.BzS3.wfun, abs_mul]
  calc |Real.log (X : ℝ) - α| * |Real.log (X : ℝ) - β|
      ≤ (2 * (1 + |Real.log (2 * (X : ℝ)) - α|)) * (2 * (1 + |Real.log (2 * (X : ℝ)) - β|)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = 4 * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|) := by ring

private lemma log_succ_sub_log_bounds (m : ℕ) (hm : 1 ≤ m) :
    1 / ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) ∧
      Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) ≤ 1 / (m : ℝ) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hx : (0 : ℝ) < ((m : ℝ) + 1) / (m : ℝ) := by positivity
  have hdiv : Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)
      = Real.log (((m : ℝ) + 1) / (m : ℝ)) :=
    (Real.log_div (by positivity) (ne_of_gt hm0)).symm
  constructor
  · rw [hdiv]
    have h := Real.one_sub_inv_le_log_of_pos hx
    have heq : 1 - (((m : ℝ) + 1) / (m : ℝ))⁻¹ = 1 / ((m : ℝ) + 1) := by
      rw [inv_div]; field_simp; ring
    rwa [heq] at h
  · rw [hdiv]
    have h := Real.log_le_sub_one_of_pos hx
    have heq : ((m : ℝ) + 1) / (m : ℝ) - 1 = 1 / (m : ℝ) := by
      field_simp; ring
    rwa [heq] at h

private lemma wfun_diff_le (m : ℕ) (hm : 1 ≤ m) (α β : ℝ) :
    |LinnikAreas.Density4.BzS3.wfun α β (m + 1) - LinnikAreas.Density4.BzS3.wfun α β m|
      ≤ (1 / (m : ℝ)) * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  obtain ⟨hδlb, hδub⟩ := log_succ_sub_log_bounds m hm
  have hcast : (((m + 1 : ℕ)) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  have hbound : |Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)| ≤ 1 / (m : ℝ) := by
    rw [abs_of_nonneg (le_trans (by positivity) hδlb)]
    exact hδub
  simp only [LinnikAreas.Density4.BzS3.wfun, hcast]
  have hfac : (Real.log ((m : ℝ) + 1) - α) * (Real.log ((m : ℝ) + 1) - β)
      - (Real.log (m : ℝ) - α) * (Real.log (m : ℝ) - β)
      = (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ))
        * ((Real.log ((m : ℝ) + 1) - α) + (Real.log (m : ℝ) - β)) := by ring
  rw [hfac, abs_mul]
  have h2 : |(Real.log ((m : ℝ) + 1) - α) + (Real.log (m : ℝ) - β)|
      ≤ |Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1 / (m : ℝ) := by
    have hsplit : (Real.log ((m : ℝ) + 1) - α) + (Real.log (m : ℝ) - β)
        = (Real.log (m : ℝ) - α) + (Real.log (m : ℝ) - β)
          + (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) := by ring
    calc |(Real.log ((m : ℝ) + 1) - α) + (Real.log (m : ℝ) - β)|
        = |((Real.log (m : ℝ) - α) + (Real.log (m : ℝ) - β))
            + (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ))| := by rw [hsplit]
      _ ≤ |(Real.log (m : ℝ) - α) + (Real.log (m : ℝ) - β)|
            + |Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)| := abs_add_le _ _
      _ ≤ (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β|) + 1 / (m : ℝ) :=
          add_le_add (abs_add_le _ _) hbound
  have hone : (1 : ℝ) ≤ 1 / (m : ℝ) * (m : ℝ) := by
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hm0)]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  calc |Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)|
        * |(Real.log ((m : ℝ) + 1) - α) + (Real.log (m : ℝ) - β)|
      ≤ (1 / (m : ℝ)) * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1 / (m : ℝ)) :=
        mul_le_mul hbound h2 (abs_nonneg _) (by positivity)
    _ ≤ (1 / (m : ℝ)) * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1) := by
        have h3 : (0 : ℝ) ≤ |Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| := by positivity
        have : (1 : ℝ) / (m : ℝ) ≤ 1 := by
          rw [div_le_one hm0]; exact hm1
        nlinarith [h3, this, hm0]

/-! ## The Abel weight, the telescoping function and its increment -/

private lemma sqrt_div_self (m : ℕ) (hm : 1 ≤ m) :
    Real.sqrt (m : ℝ) / (m : ℝ) = 1 / Real.sqrt (m : ℝ) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hs : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos_of_pos hm0
  rw [div_eq_div_iff (ne_of_gt hm0) (ne_of_gt hs), one_mul, ← pow_two, Real.sq_sqrt hm0.le]

private lemma inv_mul_sqrt_eq (m : ℕ) (hm : 1 ≤ m) :
    (1 / (m : ℝ)) * Real.sqrt (m : ℝ) = 1 / Real.sqrt (m : ℝ) := by
  rw [show (1 / (m : ℝ)) * Real.sqrt (m : ℝ) = Real.sqrt (m : ℝ) / (m : ℝ) from by ring,
    sqrt_div_self m hm]

private def S3GF (α β : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * ((Real.log (n : ℝ) - α - 1) * (Real.log (n : ℝ) - β - 1) + 1)

private def S3Geta (α β : ℝ) (m : ℕ) : ℝ :=
  LinnikAreas.Density4.BzS3.wfun α β m - (S3GF α β (m + 1) - S3GF α β m)

private lemma sum_Icc_telescope (f : ℕ → ℝ) (X : ℕ) :
    (∑ m ∈ Finset.Icc 1 X, (f (m + 1) - f m)) = f (X + 1) - f 1 := by
  induction X with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
    ring

private lemma eta_eq (m : ℕ) (α β : ℝ) :
    S3Geta α β m
      = (Real.log ((m : ℝ) + 1) + Real.log (m : ℝ) - α - β)
          * (1 - ((m : ℝ) + 1) * (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))
        + ((Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) * (2 * (m : ℝ) + 1) - 2) := by
  simp only [S3Geta, S3GF, LinnikAreas.Density4.BzS3.wfun, Nat.cast_add, Nat.cast_one]
  ring

private lemma eta_abs_le (m : ℕ) (hm : 1 ≤ m) (α β : ℝ) :
    |S3Geta α β m| ≤ (1 / (m : ℝ)) * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 2) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  obtain ⟨hδlb, hδub⟩ := log_succ_sub_log_bounds m hm
  have hδnn : 0 ≤ Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) := le_trans (by positivity) hδlb
  have hmpos : 0 < (m : ℝ) + 1 := by linarith
  have h1 : |1 - ((m : ℝ) + 1) * (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ))|
      ≤ 1 / (m : ℝ) := by
    rw [abs_le]
    constructor
    · have hup := mul_le_mul_of_nonneg_left hδub (le_of_lt hmpos)
      have heq : ((m : ℝ) + 1) * (1 / (m : ℝ)) = 1 + 1 / (m : ℝ) := by
        field_simp
      linarith [hup, heq.le]
    · have hlow := mul_le_mul_of_nonneg_left hδlb (le_of_lt hmpos)
      have heq : ((m : ℝ) + 1) * (1 / ((m : ℝ) + 1)) = 1 := by
        field_simp
      have hone : (1 : ℝ) ≤ 1 / (m : ℝ) * (m : ℝ) := by
        rw [one_div, inv_mul_cancel₀ (ne_of_gt hm0)]
      linarith [hlow, heq.le, hone]
  have h2 : |(Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) * (2 * (m : ℝ) + 1) - 2|
      ≤ 1 / (m : ℝ) := by
    rw [abs_le]
    constructor
    · have hlow := mul_le_mul_of_nonneg_left hδlb (by positivity : (0 : ℝ) ≤ 2 * (m : ℝ) + 1)
      have heq : (1 / ((m : ℝ) + 1)) * (2 * (m : ℝ) + 1) = 2 - 1 / ((m : ℝ) + 1) := by
        field_simp; ring
      have hmono : 1 / ((m : ℝ) + 1) ≤ 1 / (m : ℝ) := by
        rw [div_le_div_iff₀ hmpos hm0, one_mul, one_mul]
        linarith [hm0]
      linarith [hlow, heq.le, hmono]
    · have hup := mul_le_mul_of_nonneg_left hδub (by positivity : (0 : ℝ) ≤ 2 * (m : ℝ) + 1)
      have heq : (1 / (m : ℝ)) * (2 * (m : ℝ) + 1) = 2 + 1 / (m : ℝ) := by
        field_simp
      linarith [hup, heq.le]
  have hA : |Real.log ((m : ℝ) + 1) + Real.log (m : ℝ) - α - β|
      ≤ |Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1 / (m : ℝ) := by
    have hsplit : Real.log ((m : ℝ) + 1) + Real.log (m : ℝ) - α - β
        = ((Real.log (m : ℝ) - α) + (Real.log (m : ℝ) - β))
          + (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) := by ring
    rw [hsplit]
    have hb : |Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)| ≤ 1 / (m : ℝ) := by
      rw [abs_of_nonneg hδnn]; exact hδub
    calc |((Real.log (m : ℝ) - α) + (Real.log (m : ℝ) - β))
          + (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ))|
        ≤ |(Real.log (m : ℝ) - α) + (Real.log (m : ℝ) - β)|
          + |Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)| := abs_add_le _ _
      _ ≤ (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β|) + 1 / (m : ℝ) :=
          add_le_add (abs_add_le _ _) hb
  have hSnn : (0 : ℝ) ≤ |Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| := by positivity
  have h1mnn : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  rw [eta_eq m α β]
  calc |(Real.log ((m : ℝ) + 1) + Real.log (m : ℝ) - α - β)
        * (1 - ((m : ℝ) + 1) * (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))
        + ((Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) * (2 * (m : ℝ) + 1) - 2)|
      ≤ |(Real.log ((m : ℝ) + 1) + Real.log (m : ℝ) - α - β)
          * (1 - ((m : ℝ) + 1) * (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)))|
        + |(Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) * (2 * (m : ℝ) + 1) - 2| := abs_add_le _ _
    _ = |Real.log ((m : ℝ) + 1) + Real.log (m : ℝ) - α - β|
          * |1 - ((m : ℝ) + 1) * (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ))|
        + |(Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) * (2 * (m : ℝ) + 1) - 2| := by
        rw [abs_mul]
    _ ≤ (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1 / (m : ℝ)) * (1 / (m : ℝ))
          + 1 / (m : ℝ) :=
        add_le_add (mul_le_mul hA h1 (abs_nonneg _) (by positivity)) h2
    _ ≤ (1 / (m : ℝ)) * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 2) := by
        have hle : (1 : ℝ) / (m : ℝ) ≤ 1 := by rw [div_le_one hm0]; exact hm1
        have hsq : (1 : ℝ) / (m : ℝ) * (1 / (m : ℝ)) ≤ 1 / (m : ℝ) := by
          nlinarith [h1mnn, hle]
        calc (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1 / (m : ℝ)) * (1 / (m : ℝ))
              + 1 / (m : ℝ)
            = (1 / (m : ℝ)) * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β|)
              + ((1 / (m : ℝ)) * (1 / (m : ℝ)) + 1 / (m : ℝ)) := by ring
          _ ≤ (1 / (m : ℝ)) * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β|)
              + (1 / (m : ℝ) + 1 / (m : ℝ)) := by linarith [hsq]
          _ = (1 / (m : ℝ)) * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 2) := by ring

/-! ## The sharp smooth-sum estimate -/

private lemma log_pred_sub_abs_le (X : ℕ) (hX : 2 ≤ X) (γ : ℝ) :
    |Real.log (((X - 1 : ℕ)) : ℝ) - γ| ≤ |Real.log (X : ℝ) - γ| + 1 := by
  have h1 : 1 ≤ X - 1 := by omega
  have hδ := (log_succ_sub_log_bounds (X - 1) h1).2
  have hcast : ((X - 1 : ℕ) : ℝ) + 1 = (X : ℝ) := by
    have h : X - 1 + 1 = X := by omega
    rw [← h]; push_cast; ring
  have hp0 : (0 : ℝ) < (((X - 1 : ℕ)) : ℝ) := by
    exact_mod_cast (by omega : 0 < X - 1)
  have hδ' : Real.log (X : ℝ) - Real.log (((X - 1 : ℕ)) : ℝ) ≤ 1 := by
    have h := hδ
    rw [hcast] at h
    have h2 : 1 / (((X - 1 : ℕ)) : ℝ) ≤ 1 := by
      rw [div_le_one hp0]; exact_mod_cast h1
    linarith [h, h2]
  have hle0 : Real.log (((X - 1 : ℕ)) : ℝ) - Real.log (X : ℝ) ≤ 0 := by
    have hmono : Real.log (((X - 1 : ℕ)) : ℝ) ≤ Real.log (X : ℝ) :=
      Real.log_le_log hp0 (by exact_mod_cast (by omega : X - 1 ≤ X))
    linarith
  have habs : |Real.log (((X - 1 : ℕ)) : ℝ) - Real.log (X : ℝ)| ≤ 1 := by
    rw [abs_of_nonpos hle0]
    linarith [hδ']
  have hsplit : Real.log (((X - 1 : ℕ)) : ℝ) - γ
      = (Real.log (((X - 1 : ℕ)) : ℝ) - Real.log (X : ℝ)) + (Real.log (X : ℝ) - γ) := by ring
  rw [hsplit]
  calc |(Real.log (((X - 1 : ℕ)) : ℝ) - Real.log (X : ℝ)) + (Real.log (X : ℝ) - γ)|
      ≤ |Real.log (((X - 1 : ℕ)) : ℝ) - Real.log (X : ℝ)| + |Real.log (X : ℝ) - γ| :=
        abs_add_le _ _
    _ ≤ |Real.log (X : ℝ) - γ| + 1 := by linarith [habs]

private lemma smooth_shift_sharp_local :
    ∃ K : ℝ, 0 < K ∧ ∀ (X : ℕ) (α β : ℝ), 2 ≤ X → 0 ≤ α → 0 ≤ β →
      |(∑ m ∈ Finset.Icc 1 X, LinnikAreas.Density4.BzS3.wfun α β m)
        - (X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1)|
      ≤ K * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|)
          * Real.sqrt (X : ℝ) := by
  refine ⟨400, by norm_num, ?_⟩
  intro X α β hX hα hβ
  have hX1 : 1 ≤ X := by omega
  set A := |Real.log (2 * (X : ℝ)) - α| with hAdef
  set B := |Real.log (2 * (X : ℝ)) - β| with hBdef
  have hAnn : 0 ≤ A := by rw [hAdef]; exact abs_nonneg _
  have hBnn : 0 ≤ B := by rw [hBdef]; exact abs_nonneg _
  have hQ1 : (1 : ℝ) ≤ (1 + A) * (1 + B) := by nlinarith
  have hQnn : (0 : ℝ) ≤ (1 + A) * (1 + B) := by positivity
  have hsqnn : (0 : ℝ) ≤ Real.sqrt (X : ℝ) := Real.sqrt_nonneg _
  have hsq1 : (1 : ℝ) ≤ Real.sqrt (X : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hX1)
  have hLXα : |Real.log (X : ℝ) - α| ≤ 2 * (1 + A) := by
    rw [hAdef]; exact log_two_mul_sub_abs_bound X α
  have hLXβ : |Real.log (X : ℝ) - β| ≤ 2 * (1 + B) := by
    rw [hBdef]; exact log_two_mul_sub_abs_bound X β
  have htel : (∑ m ∈ Finset.Icc 1 X, LinnikAreas.Density4.BzS3.wfun α β m) - S3GF α β X
      = (∑ m ∈ Finset.Icc 1 X, S3Geta α β m) + (S3GF α β (X + 1) - S3GF α β X)
        - S3GF α β 1 := by
    have h1 : (∑ m ∈ Finset.Icc 1 X, LinnikAreas.Density4.BzS3.wfun α β m)
        = (∑ m ∈ Finset.Icc 1 X, (S3GF α β (m + 1) - S3GF α β m))
          + ∑ m ∈ Finset.Icc 1 X, S3Geta α β m := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [S3Geta]
      ring
    rw [h1, sum_Icc_telescope (S3GF α β) X]
    ring
  have hSumEta : |∑ m ∈ Finset.Icc 1 X, S3Geta α β m|
      ≤ 210 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := by
    have hterm : ∀ m ∈ Finset.Icc 1 X, |S3Geta α β m|
        ≤ (1 / (m : ℝ)) * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 2) := by
      intro m hm
      exact eta_abs_le m (Finset.mem_Icc.mp hm).1 α β
    have hsum : (∑ k ∈ Finset.Icc 1 X,
          (1 / (k : ℝ)) * (|Real.log (k : ℝ) - α| + |Real.log (k : ℝ) - β| + 2))
        = (∑ k ∈ Finset.Icc 1 X, (1 / (k : ℝ)) * |Real.log (k : ℝ) - α|)
          + (∑ k ∈ Finset.Icc 1 X, (1 / (k : ℝ)) * |Real.log (k : ℝ) - β|)
          + 2 * (∑ k ∈ Finset.Icc 1 X, (1 / (k : ℝ))) := by
      have hpt : ∀ k ∈ Finset.Icc 1 X,
          (1 / (k : ℝ)) * (|Real.log (k : ℝ) - α| + |Real.log (k : ℝ) - β| + 2)
            = ((1 / (k : ℝ)) * |Real.log (k : ℝ) - α|
                + (1 / (k : ℝ)) * |Real.log (k : ℝ) - β|) + (1 / (k : ℝ)) * 2 := by
        intro k _
        ring
      have hpt2 : (∑ k ∈ Finset.Icc 1 X,
            (1 / (k : ℝ)) * (|Real.log (k : ℝ) - α| + |Real.log (k : ℝ) - β| + 2))
          = ∑ k ∈ Finset.Icc 1 X, (((1 / (k : ℝ)) * |Real.log (k : ℝ) - α|
                + (1 / (k : ℝ)) * |Real.log (k : ℝ) - β|) + (1 / (k : ℝ)) * 2) :=
        Finset.sum_congr rfl hpt
      rw [hpt2, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      rw [show (∑ k ∈ Finset.Icc 1 X, (1 / (k : ℝ)) * 2)
          = ∑ k ∈ Finset.Icc 1 X, 2 * (1 / (k : ℝ)) from
            Finset.sum_congr rfl (fun k _ => by ring)]
    have hb1 := sum_inv_abs_log_sub_le X α
    have hb2 := sum_inv_abs_log_sub_le X β
    have hb3 := sum_inv_le_two_sqrt X
    have hb0 : (0 : ℝ) ≤ ∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ)) := by positivity
    have step : (∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ)) * |Real.log (m : ℝ) - α|)
          + (∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ)) * |Real.log (m : ℝ) - β|)
          + 2 * (∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ)))
        ≤ 20 * Real.sqrt (X : ℝ) * (1 + |Real.log (X : ℝ) - α|)
          + 20 * Real.sqrt (X : ℝ) * (1 + |Real.log (X : ℝ) - β|)
          + 2 * (2 * Real.sqrt (X : ℝ)) := by
      have h4 : 2 * (∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ))) ≤ 2 * (2 * Real.sqrt (X : ℝ)) :=
        mul_le_mul_of_nonneg_left hb3 (by norm_num)
      linarith [hb1, hb2, h4]
    have hfin : 20 * Real.sqrt (X : ℝ) * (1 + |Real.log (X : ℝ) - α|)
          + 20 * Real.sqrt (X : ℝ) * (1 + |Real.log (X : ℝ) - β|)
          + 2 * (2 * Real.sqrt (X : ℝ))
        ≤ 210 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := by
      have h5a : (1 : ℝ) + |Real.log (X : ℝ) - α| ≤ 5 * (1 + A) := by linarith [hLXα]
      have h5b : (1 : ℝ) + |Real.log (X : ℝ) - β| ≤ 5 * (1 + B) := by linarith [hLXβ]
      have hB1 : (1 : ℝ) ≤ 1 + B := by linarith
      have hA1 : (1 : ℝ) ≤ 1 + A := by linarith
      have p1 : 20 * Real.sqrt (X : ℝ) * (1 + |Real.log (X : ℝ) - α|)
          ≤ 100 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := by
        have h1 : 20 * Real.sqrt (X : ℝ) * (1 + |Real.log (X : ℝ) - α|)
            ≤ 20 * Real.sqrt (X : ℝ) * (5 * (1 + A)) :=
          mul_le_mul_of_nonneg_left h5a (by positivity)
        have h2 : 20 * Real.sqrt (X : ℝ) * (5 * (1 + A)) = 100 * (1 + A) * Real.sqrt (X : ℝ) := by
          ring
        have h3 : 100 * (1 + A) * Real.sqrt (X : ℝ)
            ≤ 100 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := by
          have hkey : 100 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ)
              - 100 * (1 + A) * Real.sqrt (X : ℝ) = 100 * (1 + A) * B * Real.sqrt (X : ℝ) := by
            ring
          have hnn : (0 : ℝ) ≤ 100 * (1 + A) * B * Real.sqrt (X : ℝ) := by positivity
          linarith [hkey, hnn]
        linarith [h1, h2.le, h3]
      have p2 : 20 * Real.sqrt (X : ℝ) * (1 + |Real.log (X : ℝ) - β|)
          ≤ 100 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := by
        have h1 : 20 * Real.sqrt (X : ℝ) * (1 + |Real.log (X : ℝ) - β|)
            ≤ 20 * Real.sqrt (X : ℝ) * (5 * (1 + B)) :=
          mul_le_mul_of_nonneg_left h5b (by positivity)
        have h2 : 20 * Real.sqrt (X : ℝ) * (5 * (1 + B)) = 100 * (1 + B) * Real.sqrt (X : ℝ) := by
          ring
        have h3 : 100 * (1 + B) * Real.sqrt (X : ℝ)
            ≤ 100 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := by
          have hkey : 100 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ)
              - 100 * (1 + B) * Real.sqrt (X : ℝ) = 100 * (1 + B) * A * Real.sqrt (X : ℝ) := by
            ring
          have hnn : (0 : ℝ) ≤ 100 * (1 + B) * A * Real.sqrt (X : ℝ) := by positivity
          linarith [hkey, hnn]
        linarith [h1, h2.le, h3]
      have p3 : 2 * (2 * Real.sqrt (X : ℝ)) ≤ 4 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := by
        have hkey : 4 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) - 2 * (2 * Real.sqrt (X : ℝ))
            = 4 * (A + B + A * B) * Real.sqrt (X : ℝ) := by ring
        have hnn : (0 : ℝ) ≤ 4 * (A + B + A * B) * Real.sqrt (X : ℝ) := by
          have hAB : (0 : ℝ) ≤ A + B + A * B := by nlinarith [hAnn, hBnn]
          positivity
        linarith [hkey, hnn]
      linarith [p1, p2, p3]
    calc |∑ m ∈ Finset.Icc 1 X, S3Geta α β m| ≤ ∑ m ∈ Finset.Icc 1 X, |S3Geta α β m| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Icc 1 X,
            (1 / (m : ℝ)) * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 2) :=
          Finset.sum_le_sum hterm
      _ = (∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ)) * |Real.log (m : ℝ) - α|)
          + (∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ)) * |Real.log (m : ℝ) - β|)
          + 2 * (∑ m ∈ Finset.Icc 1 X, (1 / (m : ℝ))) := hsum
      _ ≤ 20 * Real.sqrt (X : ℝ) * (1 + |Real.log (X : ℝ) - α|)
          + 20 * Real.sqrt (X : ℝ) * (1 + |Real.log (X : ℝ) - β|)
          + 2 * (2 * Real.sqrt (X : ℝ)) := step
      _ ≤ 210 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := hfin
  have hGdiff : |S3GF α β (X + 1) - S3GF α β X| ≤ 10 * (1 + A) * (1 + B) := by
    have hval : S3GF α β (X + 1) - S3GF α β X
        = LinnikAreas.Density4.BzS3.wfun α β X - S3Geta α β X := by
      unfold S3Geta; ring
    rw [hval]
    have hwa : |LinnikAreas.Density4.BzS3.wfun α β X| ≤ 4 * (1 + A) * (1 + B) := by
      rw [hAdef, hBdef]; exact wfun_abs_le X α β
    have heta := eta_abs_le X hX1 α β
    have hX0 : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
    have hle1 : (1 : ℝ) / (X : ℝ) ≤ 1 := by rw [div_le_one hX0]; exact_mod_cast hX1
    have hnn : (0 : ℝ) ≤ |Real.log (X : ℝ) - α| + |Real.log (X : ℝ) - β| + 2 := by positivity
    have hb : (1 / (X : ℝ)) * (|Real.log (X : ℝ) - α| + |Real.log (X : ℝ) - β| + 2)
        ≤ 2 * (1 + A) + 2 * (1 + B) + 2 := by
      have hsum2 : |Real.log (X : ℝ) - α| + |Real.log (X : ℝ) - β| + 2
          ≤ 2 * (1 + A) + 2 * (1 + B) + 2 := by linarith [hLXα, hLXβ]
      calc (1 / (X : ℝ)) * (|Real.log (X : ℝ) - α| + |Real.log (X : ℝ) - β| + 2)
          ≤ 1 * (2 * (1 + A) + 2 * (1 + B) + 2) :=
            mul_le_mul hle1 hsum2 hnn (by norm_num)
        _ = 2 * (1 + A) + 2 * (1 + B) + 2 := by ring
    calc |LinnikAreas.Density4.BzS3.wfun α β X - S3Geta α β X|
        ≤ |LinnikAreas.Density4.BzS3.wfun α β X| + |S3Geta α β X| := by
          rw [sub_eq_add_neg, ← abs_neg (S3Geta α β X)]
          exact abs_add_le _ _
      _ ≤ 4 * (1 + A) * (1 + B)
            + (1 / (X : ℝ)) * (|Real.log (X : ℝ) - α| + |Real.log (X : ℝ) - β| + 2) :=
          add_le_add hwa heta
      _ ≤ 10 * (1 + A) * (1 + B) := by
          nlinarith [hb, hQ1, hAnn, hBnn]
  have hG1 : |S3GF α β 1| ≤ 101 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := by
    have hval : S3GF α β 1 = (α + 1) * (β + 1) + 1 := by
      simp only [S3GF, Nat.cast_one, Real.log_one]
      ring
    rw [hval, abs_of_nonneg (by positivity)]
    have hαb : α + 1 ≤ (Real.log (2 * (X : ℝ)) + 1) * (1 + A) := by
      rw [hAdef]; exact alpha_add_one_le X α
    have hβb : β + 1 ≤ (Real.log (2 * (X : ℝ)) + 1) * (1 + B) := by
      rw [hBdef]; exact alpha_add_one_le X β
    have hLs : (Real.log (2 * (X : ℝ)) + 1) ^ 2 ≤ 100 * Real.sqrt (X : ℝ) :=
      log_two_mul_add_one_sq_le X hX
    have h2nn : (0 : ℝ) ≤ β + 1 := by linarith
    have h3nn : (0 : ℝ) ≤ (Real.log (2 * (X : ℝ)) + 1) * (1 + A) := by
      have h2X : (1 : ℝ) ≤ 2 * (X : ℝ) := by
        have : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
        linarith
      have hLn : (0 : ℝ) ≤ Real.log (2 * (X : ℝ)) := Real.log_nonneg h2X
      have h1A : (0 : ℝ) < 1 + A := by linarith
      calc (0 : ℝ) = 0 * (1 + A) := by ring
        _ ≤ (Real.log (2 * (X : ℝ)) + 1) * (1 + A) :=
            mul_le_mul_of_nonneg_right (by linarith) h1A.le
    have hmain : (α + 1) * (β + 1)
        ≤ (Real.log (2 * (X : ℝ)) + 1) ^ 2 * (1 + A) * (1 + B) := by
      calc (α + 1) * (β + 1)
          ≤ ((Real.log (2 * (X : ℝ)) + 1) * (1 + A))
              * ((Real.log (2 * (X : ℝ)) + 1) * (1 + B)) :=
            mul_le_mul hαb hβb h2nn h3nn
        _ = (Real.log (2 * (X : ℝ)) + 1) ^ 2 * (1 + A) * (1 + B) := by ring
    have h100 : (Real.log (2 * (X : ℝ)) + 1) ^ 2 * (1 + A) * (1 + B)
        ≤ 100 * Real.sqrt (X : ℝ) * (1 + A) * (1 + B) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hLs (by linarith [hAnn])) (by linarith [hBnn])
    have hone : (1 : ℝ) ≤ (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := by nlinarith [hQ1, hsq1]
    calc (α + 1) * (β + 1) + 1
        ≤ (Real.log (2 * (X : ℝ)) + 1) ^ 2 * (1 + A) * (1 + B) + 1 := by linarith [hmain]
      _ ≤ 100 * Real.sqrt (X : ℝ) * (1 + A) * (1 + B)
            + (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := by linarith [h100, hone]
      _ = 101 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := by ring
  have hGX : S3GF α β X
      = (X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1) := rfl
  rw [← hGX, htel]
  have htri : |(∑ m ∈ Finset.Icc 1 X, S3Geta α β m) + (S3GF α β (X + 1) - S3GF α β X)
        - S3GF α β 1|
      ≤ |∑ m ∈ Finset.Icc 1 X, S3Geta α β m| + |S3GF α β (X + 1) - S3GF α β X|
        + |S3GF α β 1| := by
    have h2 : (∑ m ∈ Finset.Icc 1 X, S3Geta α β m) + (S3GF α β (X + 1) - S3GF α β X)
        - S3GF α β 1
        = ((∑ m ∈ Finset.Icc 1 X, S3Geta α β m) + (S3GF α β (X + 1) - S3GF α β X))
          + (-(S3GF α β 1)) := by ring
    rw [h2]
    calc |((∑ m ∈ Finset.Icc 1 X, S3Geta α β m) + (S3GF α β (X + 1) - S3GF α β X))
          + (-(S3GF α β 1))|
        ≤ |(∑ m ∈ Finset.Icc 1 X, S3Geta α β m) + (S3GF α β (X + 1) - S3GF α β X)|
          + |-(S3GF α β 1)| := abs_add_le _ _
      _ ≤ (|∑ m ∈ Finset.Icc 1 X, S3Geta α β m| + |S3GF α β (X + 1) - S3GF α β X|)
          + |S3GF α β 1| := by
          rw [abs_neg]
          linarith [abs_add_le (∑ m ∈ Finset.Icc 1 X, S3Geta α β m)
            (S3GF α β (X + 1) - S3GF α β X)]
      _ = |∑ m ∈ Finset.Icc 1 X, S3Geta α β m| + |S3GF α β (X + 1) - S3GF α β X|
          + |S3GF α β 1| := by ring
  calc |(∑ m ∈ Finset.Icc 1 X, S3Geta α β m) + (S3GF α β (X + 1) - S3GF α β X)
        - S3GF α β 1|
      ≤ |∑ m ∈ Finset.Icc 1 X, S3Geta α β m| + |S3GF α β (X + 1) - S3GF α β X|
        + |S3GF α β 1| := htri
    _ ≤ 210 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) + 10 * (1 + A) * (1 + B)
          + 101 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) :=
        add_le_add (add_le_add hSumEta hGdiff) hG1
    _ ≤ 321 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := by
        have h10 : 10 * (1 + A) * (1 + B) ≤ 10 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := by
          calc 10 * (1 + A) * (1 + B) = 10 * (1 + A) * (1 + B) * 1 := by ring
            _ ≤ 10 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) :=
                mul_le_mul_of_nonneg_left hsq1 (by positivity)
        linarith [h10]
    _ ≤ 400 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := by
        have hnn : (0 : ℝ) ≤ (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := by positivity
        have h321 := mul_le_mul_of_nonneg_right (by norm_num : (321 : ℝ) ≤ 400) hnn
        linarith [h321]

/-! ## The sharp Abel error estimate -/

private lemma abel_error_sharp_local :
    ∃ K : ℝ, 0 < K ∧ ∀ (c X : ℕ) (α β : ℝ),
      1 ≤ c → 2 ≤ X → 0 ≤ α → 0 ≤ β →
      |s3Delta c X * LinnikAreas.Density4.BzS3.wfun α β X
        + ∑ m ∈ Finset.Icc 1 (X - 1),
            (LinnikAreas.Density4.BzS3.wfun α β m
              - LinnikAreas.Density4.BzS3.wfun α β (m + 1)) * s3Delta c m|
      ≤ K * s3Sig c * Real.sqrt (X : ℝ)
          * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|) := by
  obtain ⟨C₀, hC₀pos, hDelta⟩ := s3Delta_bound
  have hC₀nn : (0 : ℝ) ≤ C₀ := le_of_lt hC₀pos
  refine ⟨300 * C₀, by positivity, ?_⟩
  intro c X α β hc hX hα hβ
  have hX1 : 1 ≤ X := by omega
  set A := |Real.log (2 * (X : ℝ)) - α| with hAdef
  set B := |Real.log (2 * (X : ℝ)) - β| with hBdef
  have hAnn : 0 ≤ A := by rw [hAdef]; exact abs_nonneg _
  have hBnn : 0 ≤ B := by rw [hBdef]; exact abs_nonneg _
  have hQnn : (0 : ℝ) ≤ (1 + A) * (1 + B) := by positivity
  have hQ1 : (1 : ℝ) ≤ (1 + A) * (1 + B) := by nlinarith
  have hsgnn : (0 : ℝ) ≤ s3Sig c := s3Sig_nonneg c
  have hsqnn : (0 : ℝ) ≤ Real.sqrt (X : ℝ) := Real.sqrt_nonneg _
  have hsq1 : (1 : ℝ) ≤ Real.sqrt (X : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hX1)
  have hLXα : |Real.log (X : ℝ) - α| ≤ 2 * (1 + A) := by
    rw [hAdef]; exact log_two_mul_sub_abs_bound X α
  have hLXβ : |Real.log (X : ℝ) - β| ≤ 2 * (1 + B) := by
    rw [hBdef]; exact log_two_mul_sub_abs_bound X β
  have hcnt : ∀ m : ℕ, 1 ≤ m → |s3Delta c m| ≤ C₀ * s3Sig c * Real.sqrt (m : ℝ) :=
    fun m hm => hDelta c m hc hm
  have ht1 : |s3Delta c X * LinnikAreas.Density4.BzS3.wfun α β X|
      ≤ C₀ * s3Sig c * Real.sqrt (X : ℝ) * (4 * (1 + A) * (1 + B)) := by
    rw [abs_mul]
    have hw : |LinnikAreas.Density4.BzS3.wfun α β X| ≤ 4 * (1 + A) * (1 + B) := by
      rw [hAdef, hBdef]; exact wfun_abs_le X α β
    exact mul_le_mul (hcnt X hX1) hw (abs_nonneg _) (by positivity)
  have ht2 : |∑ m ∈ Finset.Icc 1 (X - 1),
        (LinnikAreas.Density4.BzS3.wfun α β m
          - LinnikAreas.Density4.BzS3.wfun α β (m + 1)) * s3Delta c m|
      ≤ C₀ * s3Sig c * (250 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ)) := by
    have hterm : ∀ m ∈ Finset.Icc 1 (X - 1),
        |(LinnikAreas.Density4.BzS3.wfun α β m
          - LinnikAreas.Density4.BzS3.wfun α β (m + 1)) * s3Delta c m|
        ≤ C₀ * s3Sig c * ((1 / Real.sqrt (m : ℝ))
            * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1)) := by
      intro m hm
      obtain ⟨hm1, _⟩ := Finset.mem_Icc.mp hm
      rw [abs_mul]
      have hd : |LinnikAreas.Density4.BzS3.wfun α β m
            - LinnikAreas.Density4.BzS3.wfun α β (m + 1)|
          ≤ (1 / (m : ℝ)) * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1) := by
        rw [abs_sub_comm]; exact wfun_diff_le m hm1 α β
      calc |LinnikAreas.Density4.BzS3.wfun α β m
              - LinnikAreas.Density4.BzS3.wfun α β (m + 1)| * |s3Delta c m|
          ≤ ((1 / (m : ℝ)) * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1))
              * (C₀ * s3Sig c * Real.sqrt (m : ℝ)) :=
            mul_le_mul hd (hcnt m hm1) (abs_nonneg _) (by positivity)
        _ = C₀ * s3Sig c * ((1 / Real.sqrt (m : ℝ))
              * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1)) := by
            have hs1 : (1 / (m : ℝ)) * Real.sqrt (m : ℝ) = 1 / Real.sqrt (m : ℝ) :=
              inv_mul_sqrt_eq m hm1
            rw [show ((1 / (m : ℝ)) * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1))
                  * (C₀ * s3Sig c * Real.sqrt (m : ℝ))
                = C₀ * s3Sig c * ((1 / (m : ℝ)) * Real.sqrt (m : ℝ)
                    * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1)) from by ring, hs1]
    have hsum : (∑ m ∈ Finset.Icc 1 (X - 1), ((1 / Real.sqrt (m : ℝ))
            * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β|) + (1 / Real.sqrt (m : ℝ))))
        = (∑ m ∈ Finset.Icc 1 (X - 1), (1 / Real.sqrt (m : ℝ)) * |Real.log (m : ℝ) - α|)
          + (∑ m ∈ Finset.Icc 1 (X - 1), (1 / Real.sqrt (m : ℝ)) * |Real.log (m : ℝ) - β|)
          + (∑ m ∈ Finset.Icc 1 (X - 1), (1 / Real.sqrt (m : ℝ))) := by
      calc (∑ m ∈ Finset.Icc 1 (X - 1), ((1 / Real.sqrt (m : ℝ))
            * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β|) + (1 / Real.sqrt (m : ℝ))))
          = ∑ m ∈ Finset.Icc 1 (X - 1), (((1 / Real.sqrt (m : ℝ)) * |Real.log (m : ℝ) - α|
              + (1 / Real.sqrt (m : ℝ)) * |Real.log (m : ℝ) - β|)
              + (1 / Real.sqrt (m : ℝ))) := by
            apply Finset.sum_congr rfl
            intro m _
            ring
        _ = (∑ m ∈ Finset.Icc 1 (X - 1), ((1 / Real.sqrt (m : ℝ)) * |Real.log (m : ℝ) - α|
              + (1 / Real.sqrt (m : ℝ)) * |Real.log (m : ℝ) - β|))
            + ∑ m ∈ Finset.Icc 1 (X - 1), (1 / Real.sqrt (m : ℝ)) :=
            Finset.sum_add_distrib
        _ = ((∑ m ∈ Finset.Icc 1 (X - 1), (1 / Real.sqrt (m : ℝ)) * |Real.log (m : ℝ) - α|)
            + ∑ m ∈ Finset.Icc 1 (X - 1), (1 / Real.sqrt (m : ℝ)) * |Real.log (m : ℝ) - β|)
            + ∑ m ∈ Finset.Icc 1 (X - 1), (1 / Real.sqrt (m : ℝ)) := by
            rw [Finset.sum_add_distrib]
    have hsum' : (∑ m ∈ Finset.Icc 1 (X - 1), (1 / Real.sqrt (m : ℝ))
            * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1))
        = (∑ m ∈ Finset.Icc 1 (X - 1), (1 / Real.sqrt (m : ℝ)) * |Real.log (m : ℝ) - α|)
          + (∑ m ∈ Finset.Icc 1 (X - 1), (1 / Real.sqrt (m : ℝ)) * |Real.log (m : ℝ) - β|)
          + (∑ m ∈ Finset.Icc 1 (X - 1), (1 / Real.sqrt (m : ℝ))) := by
      rw [show (∑ m ∈ Finset.Icc 1 (X - 1), (1 / Real.sqrt (m : ℝ))
            * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1))
          = ∑ m ∈ Finset.Icc 1 (X - 1), ((1 / Real.sqrt (m : ℝ))
              * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β|) + (1 / Real.sqrt (m : ℝ))) from
            Finset.sum_congr rfl (fun m _ => by ring)]
      rw [hsum]
    have hb1 := sum_inv_sqrt_abs_log_sub_le (X - 1) α
    have hb2 := sum_inv_sqrt_abs_log_sub_le (X - 1) β
    have hb3 := sum_inv_sqrt_le (X - 1)
    have hsqX : Real.sqrt (((X - 1 : ℕ)) : ℝ) ≤ Real.sqrt (X : ℝ) :=
      Real.sqrt_le_sqrt (by exact_mod_cast (by omega : X - 1 ≤ X))
    have hpredα : |Real.log (((X - 1 : ℕ)) : ℝ) - α| ≤ |Real.log (X : ℝ) - α| + 1 :=
      log_pred_sub_abs_le X hX α
    have hpredβ : |Real.log (((X - 1 : ℕ)) : ℝ) - β| ≤ |Real.log (X : ℝ) - β| + 1 :=
      log_pred_sub_abs_le X hX β
    have hb1' : (∑ m ∈ Finset.Icc 1 (X - 1), (1 / Real.sqrt (m : ℝ)) * |Real.log (m : ℝ) - α|)
        ≤ 120 * (1 + A) * Real.sqrt (X : ℝ) := by
      have h6 : (1 : ℝ) + |Real.log (((X - 1 : ℕ)) : ℝ) - α| ≤ 6 * (1 + A) := by
        linarith [hpredα, hLXα]
      have hy : (0 : ℝ) ≤ 1 + |Real.log (((X - 1 : ℕ)) : ℝ) - α| := by positivity
      have hstep1 : 20 * Real.sqrt (((X - 1 : ℕ)) : ℝ)
            * (1 + |Real.log (((X - 1 : ℕ)) : ℝ) - α|)
          ≤ 20 * Real.sqrt (X : ℝ) * (1 + |Real.log (((X - 1 : ℕ)) : ℝ) - α|) := by
        have hmono : 20 * Real.sqrt (((X - 1 : ℕ)) : ℝ) ≤ 20 * Real.sqrt (X : ℝ) := by
          linarith [hsqX]
        exact mul_le_mul_of_nonneg_right hmono hy
      have hstep2 : 20 * Real.sqrt (X : ℝ) * (1 + |Real.log (((X - 1 : ℕ)) : ℝ) - α|)
          ≤ 20 * Real.sqrt (X : ℝ) * (6 * (1 + A)) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
      calc (∑ m ∈ Finset.Icc 1 (X - 1), (1 / Real.sqrt (m : ℝ)) * |Real.log (m : ℝ) - α|)
          ≤ 20 * Real.sqrt (((X - 1 : ℕ)) : ℝ)
              * (1 + |Real.log (((X - 1 : ℕ)) : ℝ) - α|) := hb1
        _ ≤ 20 * Real.sqrt (X : ℝ) * (1 + |Real.log (((X - 1 : ℕ)) : ℝ) - α|) := hstep1
        _ ≤ 20 * Real.sqrt (X : ℝ) * (6 * (1 + A)) := hstep2
        _ = 120 * (1 + A) * Real.sqrt (X : ℝ) := by ring
    have hb2' : (∑ m ∈ Finset.Icc 1 (X - 1), (1 / Real.sqrt (m : ℝ)) * |Real.log (m : ℝ) - β|)
        ≤ 120 * (1 + B) * Real.sqrt (X : ℝ) := by
      have h6 : (1 : ℝ) + |Real.log (((X - 1 : ℕ)) : ℝ) - β| ≤ 6 * (1 + B) := by
        linarith [hpredβ, hLXβ]
      have hy : (0 : ℝ) ≤ 1 + |Real.log (((X - 1 : ℕ)) : ℝ) - β| := by positivity
      have hstep1 : 20 * Real.sqrt (((X - 1 : ℕ)) : ℝ)
            * (1 + |Real.log (((X - 1 : ℕ)) : ℝ) - β|)
          ≤ 20 * Real.sqrt (X : ℝ) * (1 + |Real.log (((X - 1 : ℕ)) : ℝ) - β|) := by
        have hmono : 20 * Real.sqrt (((X - 1 : ℕ)) : ℝ) ≤ 20 * Real.sqrt (X : ℝ) := by
          linarith [hsqX]
        exact mul_le_mul_of_nonneg_right hmono hy
      have hstep2 : 20 * Real.sqrt (X : ℝ) * (1 + |Real.log (((X - 1 : ℕ)) : ℝ) - β|)
          ≤ 20 * Real.sqrt (X : ℝ) * (6 * (1 + B)) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
      calc (∑ m ∈ Finset.Icc 1 (X - 1), (1 / Real.sqrt (m : ℝ)) * |Real.log (m : ℝ) - β|)
          ≤ 20 * Real.sqrt (((X - 1 : ℕ)) : ℝ)
              * (1 + |Real.log (((X - 1 : ℕ)) : ℝ) - β|) := hb2
        _ ≤ 20 * Real.sqrt (X : ℝ) * (1 + |Real.log (((X - 1 : ℕ)) : ℝ) - β|) := hstep1
        _ ≤ 20 * Real.sqrt (X : ℝ) * (6 * (1 + B)) := hstep2
        _ = 120 * (1 + B) * Real.sqrt (X : ℝ) := by ring
    have hb3' : (∑ m ∈ Finset.Icc 1 (X - 1), (1 : ℝ) / Real.sqrt (m : ℝ))
        ≤ 2 * Real.sqrt (X : ℝ) := le_trans hb3 (by linarith [hsqX])
    have htot : (∑ m ∈ Finset.Icc 1 (X - 1), (1 / Real.sqrt (m : ℝ))
          * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1))
        ≤ 250 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := by
      rw [hsum']
      have hB1 : (1 : ℝ) ≤ 1 + B := by linarith
      have hA1 : (1 : ℝ) ≤ 1 + A := by linarith
      have e1 : 120 * (1 + A) * Real.sqrt (X : ℝ)
          ≤ 120 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := by
        have hkey : 120 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ)
            - 120 * (1 + A) * Real.sqrt (X : ℝ) = 120 * (1 + A) * B * Real.sqrt (X : ℝ) := by ring
        have hnn : (0 : ℝ) ≤ 120 * (1 + A) * B * Real.sqrt (X : ℝ) := by positivity
        linarith [hkey, hnn]
      have e2 : 120 * (1 + B) * Real.sqrt (X : ℝ)
          ≤ 120 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := by
        have hkey : 120 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ)
            - 120 * (1 + B) * Real.sqrt (X : ℝ) = 120 * (1 + B) * A * Real.sqrt (X : ℝ) := by ring
        have hnn : (0 : ℝ) ≤ 120 * (1 + B) * A * Real.sqrt (X : ℝ) := by positivity
        linarith [hkey, hnn]
      have e3 : 2 * Real.sqrt (X : ℝ) ≤ 2 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) := by
        have hkey : 2 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ) - 2 * Real.sqrt (X : ℝ)
            = 2 * (A + B + A * B) * Real.sqrt (X : ℝ) := by ring
        have hnn : (0 : ℝ) ≤ 2 * (A + B + A * B) * Real.sqrt (X : ℝ) := by
          have hAB : (0 : ℝ) ≤ A + B + A * B := by nlinarith [hAnn, hBnn]
          positivity
        linarith [hkey, hnn]
      linarith [hb1', hb2', hb3', e1, e2, e3]
    calc |∑ m ∈ Finset.Icc 1 (X - 1),
          (LinnikAreas.Density4.BzS3.wfun α β m
            - LinnikAreas.Density4.BzS3.wfun α β (m + 1)) * s3Delta c m|
        ≤ ∑ m ∈ Finset.Icc 1 (X - 1),
            |(LinnikAreas.Density4.BzS3.wfun α β m
              - LinnikAreas.Density4.BzS3.wfun α β (m + 1)) * s3Delta c m| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Icc 1 (X - 1), C₀ * s3Sig c * ((1 / Real.sqrt (m : ℝ))
            * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1)) :=
          Finset.sum_le_sum hterm
      _ = C₀ * s3Sig c * ∑ m ∈ Finset.Icc 1 (X - 1), ((1 / Real.sqrt (m : ℝ))
            * (|Real.log (m : ℝ) - α| + |Real.log (m : ℝ) - β| + 1)) := by
          rw [Finset.mul_sum]
      _ ≤ C₀ * s3Sig c * (250 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ)) :=
          mul_le_mul_of_nonneg_left htot (by positivity)
  have hfin := le_trans (abs_add_le _ _) (add_le_add ht1 ht2)
  calc |s3Delta c X * LinnikAreas.Density4.BzS3.wfun α β X
        + ∑ m ∈ Finset.Icc 1 (X - 1),
            (LinnikAreas.Density4.BzS3.wfun α β m
              - LinnikAreas.Density4.BzS3.wfun α β (m + 1)) * s3Delta c m|
      ≤ C₀ * s3Sig c * Real.sqrt (X : ℝ) * (4 * (1 + A) * (1 + B))
        + C₀ * s3Sig c * (250 * (1 + A) * (1 + B) * Real.sqrt (X : ℝ)) := hfin
    _ ≤ 300 * C₀ * s3Sig c * Real.sqrt (X : ℝ) * (1 + A) * (1 + B) := by
        have hnn : (0 : ℝ) ≤ C₀ * s3Sig c * Real.sqrt (X : ℝ) * (1 + A) * (1 + B) := by
          positivity
        have h254 := mul_le_mul_of_nonneg_right (by norm_num : (254 : ℝ) ≤ 300) hnn
        linarith [h254]

private lemma mu_sq_indicator (m : ℕ) :
    ((ArithmeticFunction.moebius m : ℤ) : ℝ) ^ 2 = if Squarefree m then 1 else 0 := by
  rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]
  split <;> simp

/-- `s3G` written as a `μ²`-weighted sum over the coprime class. -/
lemma s3G_eq_sum_ite (c X : ℕ) (α β : ℝ) :
    LinnikAreas.Density4.BzS3.s3G c α β X
      = ∑ m ∈ Finset.Icc 1 X,
          (if Nat.Coprime m c then ((ArithmeticFunction.moebius m : ℤ) : ℝ) ^ 2 else 0)
            * LinnikAreas.Density4.BzS3.wfun α β m := by
  rw [LinnikAreas.Density4.BzS3.s3G, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [LinnikAreas.Density4.BzS3.wfun]
  by_cases hc : Nat.Coprime m c
  · by_cases hs : Squarefree m
    · rw [if_pos ⟨hc, hs⟩, if_pos hc, mu_sq_indicator, if_pos hs]; ring
    · rw [if_neg (fun h => hs h.2), if_pos hc, mu_sq_indicator, if_neg hs]; ring
  · rw [if_neg (fun h => hc h.1), if_neg hc]; ring

/-- **The two-weight Abel identity for `s3G`**: subtracting `C_c·Σ_{m ≤ X} w_m` from the weighted
sum leaves exactly the Abel sum of the difference sequence `s3Delta`. -/
lemma s3G_abel (c X : ℕ) (α β : ℝ) :
    LinnikAreas.Density4.BzS3.s3G c α β X
        - LinnikAreas.Density4.BzS3.s3c c
            * (∑ m ∈ Finset.Icc 1 X, LinnikAreas.Density4.BzS3.wfun α β m)
      = s3Delta c X * LinnikAreas.Density4.BzS3.wfun α β X
        + ∑ m ∈ Finset.Icc 1 (X - 1),
            (LinnikAreas.Density4.BzS3.wfun α β m
              - LinnikAreas.Density4.BzS3.wfun α β (m + 1)) * s3Delta c m := by
  have hab := Work.LinnikAreas.Density4.BzBilin.abel_two_weights
    (fun m : ℕ => if Nat.Coprime m c then ((ArithmeticFunction.moebius m : ℤ) : ℝ) ^ 2 else 0)
    (LinnikAreas.Density4.BzS3.wfun α β) (LinnikAreas.Density4.BzS3.s3c c) X
  rw [← s3G_eq_sum_ite c X α β] at hab
  simp only [← s3Count_eq_sum_ite] at hab
  simpa only [s3Delta] using hab

/-- **Sharp two-Abel estimate comparing `s3G` with its main term `s3main`.**

`s3G c α β X = Σ_{m ≤ X, (m,c)=1, m squarefree} (log m − α)(log m − β)` and
`s3main c α β X = ζ(2)^{-1}∏_{p|c} p/(p+1) · X · ((log X − α − 1)(log X − β − 1) + 1)`
(`BzS3/S3InnerDefs.lean`), the model obtained by two Abel summations against the squarefree
coprime count `Σ_{m ≤ M,(m,c)=1} μ²(m) = C_c M + O(√M·σ_{-1/2}(c))`
(`BzBilin/sqfree_coprime_count_sigma`, sorry-free).  The claim is the matching error bound
`|s3G c α β X − s3main c α β X| ≤ K·σ_{-1/2}(c)·√X·(1+|log(2X) − α|)·(1+|log(2X) − β|)`
for `c ≥ 1`, `X ≥ 2`, `α, β ≥ 0`, with `σ_{-1/2}(c) = Σ_{d ∣ c} 1/√d`.

Verified numerically (independent Python recomputation of `s3G` from the definition): the ratio
`|s3G − s3main| / (σ_{-1/2}(c)·√X·(1+|log(2X)−α|)(1+|log(2X)−β|))` is `≤ 0.21` over
`c ∈ {1,2,6,30,210}`, `α,β ∈ {0,0.5,2,3,5}`, `X ∈ {10,100,1000,10⁴,10⁵}`; so `K = 1` (say) works.
This is the analytic heart of the `S₃` analysis (An, arXiv:2206.10104, §5): two Abel summations
of `(log m − α)` against the power-saving squarefree-coprime count; the imported
`abel_weighted_difference_bound_range` is exactly the Abel tool. -/
theorem S3GAbelSharp :
    ∃ K : ℝ, 0 < K ∧ ∀ (c X : ℕ) (α β : ℝ), 1 ≤ c → 2 ≤ X → 0 ≤ α → 0 ≤ β →
      |LinnikAreas.Density4.BzS3.s3G c α β X - LinnikAreas.Density4.BzS3.s3main c α β X| ≤
        (K * ∑ d ∈ c.divisors, 1 / Real.sqrt (d : ℝ)) * Real.sqrt (X : ℝ) *
          (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|) := by
  obtain ⟨K₁, hK₁, hSmooth⟩ := smooth_shift_sharp_local
  obtain ⟨K₂, hK₂, hAbel⟩ := abel_error_sharp_local
  refine ⟨K₁ + K₂, by linarith, ?_⟩
  intro c X α β hc hX hα hβ
  -- the two error terms of the two-weight Abel identity
  have hsmooth := hSmooth X α β hX hα hβ
  have habel := hAbel c X α β hc hX hα hβ
  have hkey := s3G_abel c X α β
  have hs3cnn : (0 : ℝ) ≤ LinnikAreas.Density4.BzS3.s3c c :=
    LinnikAreas.Density4.BzS3.s3c_nonneg c
  have hs3c1 : LinnikAreas.Density4.BzS3.s3c c ≤ 1 :=
    LinnikAreas.Density4.BzS3.s3c_le_one c
  have hsg1 : (1 : ℝ) ≤ s3Sig c := s3Sig_one_le c hc
  have hsgnn : (0 : ℝ) ≤ s3Sig c := s3Sig_nonneg c
  have hK₁nn : (0 : ℝ) ≤ K₁ := le_of_lt hK₁
  have hK₂nn : (0 : ℝ) ≤ K₂ := le_of_lt hK₂
  -- `s3main` in factored form
  have hmain : LinnikAreas.Density4.BzS3.s3main c α β X
      = LinnikAreas.Density4.BzS3.s3c c
          * ((X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1)) := by
    rw [LinnikAreas.Density4.BzS3.s3main]; ring
  -- split the difference into the smooth part and the Abel error
  have hstep : LinnikAreas.Density4.BzS3.s3G c α β X - LinnikAreas.Density4.BzS3.s3main c α β X
      = LinnikAreas.Density4.BzS3.s3c c
          * ((∑ m ∈ Finset.Icc 1 X, LinnikAreas.Density4.BzS3.wfun α β m)
              - (X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1))
        + (s3Delta c X * LinnikAreas.Density4.BzS3.wfun α β X
            + ∑ m ∈ Finset.Icc 1 (X - 1),
                (LinnikAreas.Density4.BzS3.wfun α β m
                  - LinnikAreas.Density4.BzS3.wfun α β (m + 1)) * s3Delta c m) := by
    rw [hmain]
    linarith [hkey]
  rw [hstep]
  -- the two pieces, bounded
  have hb1 : |LinnikAreas.Density4.BzS3.s3c c
        * ((∑ m ∈ Finset.Icc 1 X, LinnikAreas.Density4.BzS3.wfun α β m)
            - (X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1))|
      ≤ K₁ * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|)
          * Real.sqrt (X : ℝ) := by
    rw [abs_mul, abs_of_nonneg hs3cnn]
    calc LinnikAreas.Density4.BzS3.s3c c
          * |(∑ m ∈ Finset.Icc 1 X, LinnikAreas.Density4.BzS3.wfun α β m)
              - (X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1)|
        ≤ 1 * (K₁ * (1 + |Real.log (2 * (X : ℝ)) - α|)
            * (1 + |Real.log (2 * (X : ℝ)) - β|) * Real.sqrt (X : ℝ)) :=
          mul_le_mul hs3c1 hsmooth (abs_nonneg _) (by norm_num)
      _ = K₁ * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|)
            * Real.sqrt (X : ℝ) := by ring
  have hb2 : |s3Delta c X * LinnikAreas.Density4.BzS3.wfun α β X
        + ∑ m ∈ Finset.Icc 1 (X - 1),
            (LinnikAreas.Density4.BzS3.wfun α β m
              - LinnikAreas.Density4.BzS3.wfun α β (m + 1)) * s3Delta c m|
      ≤ K₂ * s3Sig c * Real.sqrt (X : ℝ) * (1 + |Real.log (2 * (X : ℝ)) - α|)
          * (1 + |Real.log (2 * (X : ℝ)) - β|) := habel
  -- final bookkeeping
  have hfin : K₁ * (1 + |Real.log (2 * (X : ℝ)) - α|)
        * (1 + |Real.log (2 * (X : ℝ)) - β|) * Real.sqrt (X : ℝ)
      + K₂ * s3Sig c * Real.sqrt (X : ℝ) * (1 + |Real.log (2 * (X : ℝ)) - α|)
          * (1 + |Real.log (2 * (X : ℝ)) - β|)
      ≤ (K₁ + K₂) * s3Sig c * Real.sqrt (X : ℝ) * (1 + |Real.log (2 * (X : ℝ)) - α|)
          * (1 + |Real.log (2 * (X : ℝ)) - β|) := by
    set W := 1 + |Real.log (2 * (X : ℝ)) - α| with hWdef
    set V := 1 + |Real.log (2 * (X : ℝ)) - β| with hVdef
    set R := Real.sqrt (X : ℝ) with hRdef
    have hWnn : (0 : ℝ) ≤ W := by rw [hWdef]; positivity
    have hVnn : (0 : ℝ) ≤ V := by rw [hVdef]; positivity
    have hRnn : (0 : ℝ) ≤ R := by rw [hRdef]; exact Real.sqrt_nonneg _
    have h1 : K₁ * W * V * R ≤ K₁ * s3Sig c * R * W * V := by
      have h0 : (0 : ℝ) ≤ K₁ * (R * W * V) :=
        mul_nonneg hK₁nn (mul_nonneg (mul_nonneg hRnn hWnn) hVnn)
      have h3 := mul_le_mul_of_nonneg_left hsg1 h0
      calc K₁ * W * V * R = K₁ * (R * W * V) * 1 := by ring
        _ ≤ K₁ * (R * W * V) * s3Sig c := h3
        _ = K₁ * s3Sig c * R * W * V := by ring
    have h2 : K₁ * s3Sig c * R * W * V + K₂ * s3Sig c * R * W * V
        = (K₁ + K₂) * s3Sig c * R * W * V := by ring
    rw [← h2]
    linarith [h1]
  calc |LinnikAreas.Density4.BzS3.s3c c
          * ((∑ m ∈ Finset.Icc 1 X, LinnikAreas.Density4.BzS3.wfun α β m)
              - (X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1))
        + (s3Delta c X * LinnikAreas.Density4.BzS3.wfun α β X
            + ∑ m ∈ Finset.Icc 1 (X - 1),
                (LinnikAreas.Density4.BzS3.wfun α β m
                  - LinnikAreas.Density4.BzS3.wfun α β (m + 1)) * s3Delta c m)|
      ≤ |LinnikAreas.Density4.BzS3.s3c c
          * ((∑ m ∈ Finset.Icc 1 X, LinnikAreas.Density4.BzS3.wfun α β m)
              - (X : ℝ) * ((Real.log (X : ℝ) - α - 1) * (Real.log (X : ℝ) - β - 1) + 1))|
        + |s3Delta c X * LinnikAreas.Density4.BzS3.wfun α β X
            + ∑ m ∈ Finset.Icc 1 (X - 1),
                (LinnikAreas.Density4.BzS3.wfun α β m
                  - LinnikAreas.Density4.BzS3.wfun α β (m + 1)) * s3Delta c m| := abs_add_le _ _
    _ ≤ K₁ * (1 + |Real.log (2 * (X : ℝ)) - α|) * (1 + |Real.log (2 * (X : ℝ)) - β|)
            * Real.sqrt (X : ℝ)
          + K₂ * s3Sig c * Real.sqrt (X : ℝ) * (1 + |Real.log (2 * (X : ℝ)) - α|)
              * (1 + |Real.log (2 * (X : ℝ)) - β|) := add_le_add hb1 hb2
    _ ≤ (K₁ + K₂) * s3Sig c * Real.sqrt (X : ℝ) * (1 + |Real.log (2 * (X : ℝ)) - α|)
          * (1 + |Real.log (2 * (X : ℝ)) - β|) := hfin


end

end Work.ZeroDensity.Jutila
