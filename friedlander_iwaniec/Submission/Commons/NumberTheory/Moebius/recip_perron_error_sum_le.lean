import Mathlib
import Submission.Commons.NumberTheory.Zeta.middle_min_dist_sum_le
import Submission.Commons.Analysis.PSeries.tsum_nat_rpow_neg_le
import Submission.Commons.Analysis.ExpLog.log_le_rpow_div

open scoped BigOperators
open Finset

set_option maxHeartbeats 4000000

namespace Commons.NumberTheory.Moebius

noncomputable section

lemma one_sub_inv_le_log {y : ℝ} (hy : 0 < y) : 1 - y⁻¹ ≤ Real.log y := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hy)
  rw [Real.log_inv] at h
  linarith

lemma abs_log_one_add_ge (u : ℝ) (hu1 : -1 < u) (hu2 : u ≤ 1) :
    |u| / 2 ≤ |Real.log (1 + u)| := by
  have hpos : 0 < 1 + u := by linarith
  rcases lt_or_ge 0 u with hu | hu
  · have hlog_nn : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
    rw [abs_of_nonneg (le_of_lt hu), abs_of_nonneg hlog_nn]
    have h1 : 1 - (1 + u)⁻¹ ≤ Real.log (1 + u) := one_sub_inv_le_log hpos
    have hkey : u / 2 ≤ 1 - (1 + u)⁻¹ := by
      have heq : (1:ℝ) - (1 + u)⁻¹ = u / (1 + u) := by
        field_simp
        ring
      rw [heq]
      exact div_le_div_of_nonneg_left (le_of_lt hu) hpos (by linarith)
    linarith
  · have hlog_le : Real.log (1 + u) ≤ u := by
      have := Real.log_le_sub_one_of_pos hpos; linarith
    have hlog_np : Real.log (1 + u) ≤ 0 := le_trans hlog_le hu
    rw [abs_of_nonpos hu, abs_of_nonpos hlog_np]
    linarith

lemma min_one_le_of_pos_le {y C : ℝ} (_hy : 0 < y) (h : y ≤ C) : min 1 y ≤ C := by
  rcases lt_or_ge 1 y with h1 | h1
  · rw [min_eq_left (le_of_lt h1)]; linarith
  · rw [min_eq_right h1]; exact h

lemma perron_recip_term_eq (x σ : ℝ) (hx : 0 ≤ x) {n : ℕ} (hn : 1 ≤ n) :
    (1/(n:ℝ))*(x/(n:ℝ))^σ = x^σ * (n:ℝ)^(-(1+σ)) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  rw [Real.div_rpow hx (Nat.cast_nonneg n) σ, Real.rpow_neg (le_of_lt hn0) (1+σ),
      Real.rpow_add hn0 1 σ, Real.rpow_one]
  field_simp

lemma abs_log_div_ge (x : ℝ) (hx : 0 < x) {n : ℕ}
    (hn1 : x/2 < (n:ℝ)) (hn2 : (n:ℝ) ≤ 2*x) :
    |x - (n:ℝ)| / (2*x) ≤ |Real.log (x/(n:ℝ))| := by
  have hn0 : (0:ℝ) < n := by linarith
  have hux1 : (1:ℝ)/2 < (n:ℝ)/x := by
    rw [lt_div_iff₀ hx]; linarith
  have hux2 : (n:ℝ)/x ≤ 2 := by
    rw [div_le_iff₀ hx]; linarith
  have hu_lb : -1 < (n:ℝ)/x - 1 := by linarith
  have hu_ub : (n:ℝ)/x - 1 ≤ 1 := by linarith
  have hlog := abs_log_one_add_ge ((n:ℝ)/x - 1) hu_lb hu_ub
  have h1u : 1 + ((n:ℝ)/x - 1) = (n:ℝ)/x := by ring
  rw [h1u] at hlog
  have hdiv : Real.log (x/(n:ℝ)) = - Real.log ((n:ℝ)/x) := by
    rw [Real.log_div (ne_of_gt hx) (ne_of_gt hn0),
        Real.log_div (ne_of_gt hn0) (ne_of_gt hx)]
    ring
  rw [hdiv, abs_neg]
  have hux : |(n:ℝ)/x - 1| = |x - (n:ℝ)| / x := by
    have hh : (n:ℝ)/x - 1 = ((n:ℝ) - x)/x := by field_simp
    rw [hh, abs_div, abs_of_pos hx, abs_sub_comm]
  rw [hux] at hlog
  calc |x - (n:ℝ)| / (2*x) = (|x - (n:ℝ)| / x) / 2 := by field_simp
    _ ≤ |Real.log ((n:ℝ)/x)| := hlog

lemma perron_left_term_le (x σ T : ℝ) (hx : 3 ≤ x) (_hσ : 0 < σ) (hT : 0 < T)
    {n : ℕ} (hn1 : 1 ≤ n) (hnx : (n:ℝ) ≤ x/2) :
    (1/(n:ℝ))*(x/(n:ℝ))^σ * min 1 (1/(T*|Real.log (x/(n:ℝ))|))
      ≤ x^σ * (n:ℝ)^(-(1+σ)) * (1/(T * Real.log 2)) := by
  have hx0 : 0 ≤ x := by linarith
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn1
  have hcoef : (1/(n:ℝ))*(x/(n:ℝ))^σ = x^σ * (n:ℝ)^(-(1+σ)) :=
    perron_recip_term_eq x σ hx0 hn1
  have hcoef_nn : 0 ≤ x^σ * (n:ℝ)^(-(1+σ)) :=
    mul_nonneg (Real.rpow_nonneg hx0 σ) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rw [hcoef]
  have hlog2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hxn : (2:ℝ) ≤ x/(n:ℝ) := by rw [le_div_iff₀ hn0]; linarith
  have hlog_ge : Real.log 2 ≤ |Real.log (x/(n:ℝ))| := by
    have h1 : Real.log 2 ≤ Real.log (x/(n:ℝ)) := Real.log_le_log (by norm_num) hxn
    rw [abs_of_nonneg (Real.log_nonneg (by linarith))]
    exact h1
  have habs_pos : 0 < |Real.log (x/(n:ℝ))| := lt_of_lt_of_le hlog2p hlog_ge
  have hmin : min 1 (1/(T*|Real.log (x/(n:ℝ))|)) ≤ 1/(T*Real.log 2) := by
    apply min_one_le_of_pos_le
    · exact div_pos one_pos (mul_pos hT habs_pos)
    · apply one_div_le_one_div_of_le (mul_pos hT hlog2p)
      exact mul_le_mul_of_nonneg_left hlog_ge (le_of_lt hT)
  exact mul_le_mul_of_nonneg_left hmin hcoef_nn

lemma perron_right_term_le (x σ T : ℝ) (hx : 3 ≤ x) (_hσ : 0 < σ) (hT : 0 < T)
    {n : ℕ} (hn : 2*x ≤ (n:ℝ)) :
    (1/(n:ℝ))*(x/(n:ℝ))^σ * min 1 (1/(T*|Real.log (x/(n:ℝ))|))
      ≤ x^σ * (n:ℝ)^(-(1+σ)) * (1/(T * Real.log 2)) := by
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hn0 : (0:ℝ) < n := by linarith
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1:ℝ) ≤ (n:ℝ) by linarith)
  have hcoef : (1/(n:ℝ))*(x/(n:ℝ))^σ = x^σ * (n:ℝ)^(-(1+σ)) :=
    perron_recip_term_eq x σ hx0 hn1
  have hcoef_nn : 0 ≤ x^σ * (n:ℝ)^(-(1+σ)) :=
    mul_nonneg (Real.rpow_nonneg hx0 σ) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rw [hcoef]
  have hlog2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_ge : Real.log 2 ≤ |Real.log (x/(n:ℝ))| := by
    have hxn : (2:ℝ) ≤ (n:ℝ)/x := by rw [le_div_iff₀ hxpos]; linarith
    have h1 : Real.log 2 ≤ Real.log ((n:ℝ)/x) := Real.log_le_log (by norm_num) hxn
    have hdiv : Real.log (x/(n:ℝ)) = - Real.log ((n:ℝ)/x) := by
      rw [Real.log_div (ne_of_gt hxpos) (ne_of_gt hn0),
          Real.log_div (ne_of_gt hn0) (ne_of_gt hxpos)]
      ring
    rw [hdiv, abs_neg, abs_of_nonneg (by linarith)]
    exact h1
  have habs_pos : 0 < |Real.log (x/(n:ℝ))| := lt_of_lt_of_le hlog2p hlog_ge
  have hmin : min 1 (1/(T*|Real.log (x/(n:ℝ))|)) ≤ 1/(T*Real.log 2) := by
    apply min_one_le_of_pos_le
    · exact div_pos one_pos (mul_pos hT habs_pos)
    · apply one_div_le_one_div_of_le (mul_pos hT hlog2p)
      exact mul_le_mul_of_nonneg_left hlog_ge (le_of_lt hT)
  exact mul_le_mul_of_nonneg_left hmin hcoef_nn

lemma perron_central_term_le (x σ T : ℝ) (hx : 3 ≤ x) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hT : 0 < T) {n : ℕ} (hnx1 : x/2 < (n:ℝ)) (hnx2 : (n:ℝ) ≤ 2*x) :
    (1/(n:ℝ))*(x/(n:ℝ))^σ * min 1 (1/(T*|Real.log (x/(n:ℝ))|))
      ≤ (4/x) * min 1 ((2*x)/(T*|x - (n:ℝ)|)) := by
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hn0 : (0:ℝ) < n := by linarith
  have hcoef_le : (1/(n:ℝ))*(x/(n:ℝ))^σ ≤ 4/x := by
    have h1 : 1/(n:ℝ) ≤ 2/x := by
      have hxhalf : 0 < x/2 := by linarith
      have h1 := one_div_le_one_div_of_le hxhalf (le_of_lt hnx1)
      have heq : (1:ℝ)/(x/2) = 2/x := by field_simp
      rwa [heq] at h1
    have h2 : (x/(n:ℝ))^σ ≤ 2 := by
      have hxn_le : x/(n:ℝ) ≤ 2 := by rw [div_le_iff₀ hn0]; linarith
      have a := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ x/(n:ℝ)) hxn_le (le_of_lt hσ)
      have b : (2:ℝ)^σ ≤ 2 := by
        have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hσ1
        simpa using this
      linarith
    calc (1/(n:ℝ))*(x/(n:ℝ))^σ ≤ (2/x)*2 := by
          apply mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 4/x := by ring
  have hmin : min 1 (1/(T*|Real.log (x/(n:ℝ))|)) ≤ min 1 ((2*x)/(T*|x - (n:ℝ)|)) := by
    refine min_le_min le_rfl ?_
    by_cases hnx : (n:ℝ) = x
    · rw [hnx]
      have hxne : x ≠ 0 := ne_of_gt hxpos
      rw [div_self hxne, Real.log_one, abs_zero, mul_zero, div_zero, sub_self, abs_zero,
          mul_zero, div_zero]
    · have habs_pos : 0 < |x - (n:ℝ)| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hnx))
      have hkey : |x - (n:ℝ)|/(2*x) ≤ |Real.log (x/(n:ℝ))| :=
        abs_log_div_ge x hxpos hnx1 hnx2
      have h2x : 0 < 2*x := by linarith
      have hden_pos : 0 < T * (|x - (n:ℝ)|/(2*x)) :=
        mul_pos hT (div_pos habs_pos h2x)
      have hstep : 1/(T*|Real.log (x/(n:ℝ))|) ≤ 1/(T*(|x - (n:ℝ)|/(2*x))) :=
        one_div_le_one_div_of_le hden_pos (mul_le_mul_of_nonneg_left hkey (le_of_lt hT))
      have heq : 1/(T*(|x - (n:ℝ)|/(2*x))) = (2*x)/(T*|x - (n:ℝ)|) := by
        field_simp
      rw [heq] at hstep
      exact hstep
  have hmin_nn : 0 ≤ min 1 (1/(T*|Real.log (x/(n:ℝ))|)) :=
    le_min zero_le_one (div_nonneg zero_le_one (mul_nonneg (le_of_lt hT) (abs_nonneg _)))
  have h4x : 0 ≤ 4/x := by positivity
  calc (1/(n:ℝ))*(x/(n:ℝ))^σ * min 1 (1/(T*|Real.log (x/(n:ℝ))|))
      ≤ (4/x) * min 1 (1/(T*|Real.log (x/(n:ℝ))|)) :=
        mul_le_mul_of_nonneg_right hcoef_le hmin_nn
    _ ≤ (4/x) * min 1 ((2*x)/(T*|x - (n:ℝ)|)) := mul_le_mul_of_nonneg_left hmin h4x

theorem recip_perron_error_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x σ T : ℝ, 3 ≤ x → 0 < σ → σ ≤ 1 → 2 ≤ T → T ≤ x →
      Summable (fun n : ℕ => (1 / (n : ℝ)) * (x / (n : ℝ)) ^ σ *
          min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) ∧
      (∑' n : ℕ, (1 / (n : ℝ)) * (x / (n : ℝ)) ^ σ *
          min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) ≤
        C * (x ^ σ * (1 + 1 / σ) + 1) / T := by
  refine ⟨1000, by norm_num, ?_⟩
  intro x σ T hx hσ hσ1 hT hTle
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hT0 : 0 < T := by linarith
  set a : ℕ → ℝ := fun n => (1/(n:ℝ))*(x/(n:ℝ))^σ * min 1 (1/(T*|Real.log (x/(n:ℝ))|)) with hadef
  have ha_zero : a 0 = 0 := by simp only [hadef]; simp
  have hsp : Summable (fun n : ℕ => (n:ℝ)^(-(1+σ))) := Real.summable_nat_rpow.mpr (by linarith)
  have hg0 : Summable (fun n : ℕ => x^σ * (n:ℝ)^(-(1+σ))) := hsp.mul_left _
  have ha_nn : ∀ n, 0 ≤ a n := by
    intro n
    simp only [hadef]
    apply mul_nonneg
    · apply mul_nonneg
      · positivity
      · exact Real.rpow_nonneg (by positivity) _
    · exact le_min zero_le_one
        (div_nonneg zero_le_one (mul_nonneg (le_of_lt hT0) (abs_nonneg _)))
  have ha_le : ∀ n, a n ≤ x^σ * (n:ℝ)^(-(1+σ)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [ha_zero]
      simp only [Nat.cast_zero]
      exact mul_nonneg (Real.rpow_nonneg hx0 σ) (Real.rpow_nonneg (le_refl (0:ℝ)) _)
    · simp only [hadef]
      have hcoef := perron_recip_term_eq x σ hx0 hpos
      rw [hcoef]
      have hnn : 0 ≤ x^σ * (n:ℝ)^(-(1+σ)) :=
        mul_nonneg (Real.rpow_nonneg hx0 σ) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      simpa using mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) _) hnn
  have ha : Summable a := Summable.of_nonneg_of_le ha_nn ha_le hg0
  refine ⟨ha, ?_⟩
  set N1 : ℕ := Nat.floor (x/2) with hN1
  set N2 : ℕ := Nat.floor (2*x) with hN2
  have hN1le : N1 ≤ N2 := by
    rw [hN1, hN2]; exact Nat.floor_le_floor (by linarith)
  have hN1lt : N1 + 1 ≤ N2 := by
    rw [hN2]
    apply Nat.le_floor
    have hle : (N1:ℝ) ≤ x/2 := by rw [hN1]; exact Nat.floor_le (by linarith)
    rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hsplit1 := ha.sum_add_tsum_nat_add (N1+1)
  have hab : Summable (fun i => a (i + (N1+1))) := (summable_nat_add_iff (N1+1)).mpr ha
  have hsplit2 := hab.sum_add_tsum_nat_add (N2 - N1)
  have hS1 : (∑' n, a n) = (∑ i ∈ range (N1+1), a i) + (∑' i, a (i + (N1+1))) := hsplit1.symm
  have hS2 : (∑' i, a (i + (N1+1))) =
      (∑ i ∈ range (N2-N1), a (i + (N1+1))) + (∑' i, a (i + (N2+1))) := by
    rw [← hsplit2]
    congr 1
    apply tsum_congr
    intro i
    rw [show (i + (N2 - N1)) + (N1 + 1) = i + (N2 + 1) by omega]
  have hS : (∑' n, a n) = (∑ i ∈ range (N1+1), a i)
      + (∑ i ∈ range (N2-N1), a (i + (N1+1))) + (∑' i, a (i + (N2+1))) := by
    rw [hS1, hS2]; ring
  have hP1 : (∑ i ∈ range (N1+1), a i) ≤ x^σ * (1 + 1/σ) * (1/(T * Real.log 2)) := by
    have hstep : (∑ i ∈ range (N1+1), a i)
        ≤ ∑ i ∈ range (N1+1), x^σ * (i:ℝ)^(-(1+σ)) * (1/(T*Real.log 2)) := by
      apply Finset.sum_le_sum
      intro i hi
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · subst h0
        rw [ha_zero]
        simp only [Nat.cast_zero]
        exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hx0 σ)
          (Real.rpow_nonneg (le_refl (0:ℝ)) _)) (by positivity)
      · have hile : (i:ℝ) ≤ x/2 := by
          have hir : i ≤ N1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hN1le' : (N1:ℝ) ≤ x/2 := by rw [hN1]; exact Nat.floor_le (by linarith : (0:ℝ) ≤ x/2)
          have : (i:ℝ) ≤ (N1:ℝ) := by exact_mod_cast hir
          linarith
        exact perron_left_term_le x σ T hx hσ hT0 hpos hile
    have hc_nn : 0 ≤ x^σ * (1/(T*Real.log 2)) := by positivity
    calc (∑ i ∈ range (N1+1), a i)
        ≤ ∑ i ∈ range (N1+1), x^σ * (i:ℝ)^(-(1+σ)) * (1/(T*Real.log 2)) := hstep
      _ = (x^σ * (1/(T*Real.log 2))) * ∑ i ∈ range (N1+1), (i:ℝ)^(-(1+σ)) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _ ≤ (x^σ * (1/(T*Real.log 2))) * (1 + 1/σ) := by
          apply mul_le_mul_of_nonneg_left _ hc_nn
          have h1 : (∑ i ∈ range (N1+1), (i:ℝ)^(-(1+σ))) ≤ ∑' i : ℕ, (i:ℝ)^(-(1+σ)) :=
            hsp.sum_le_tsum (range (N1+1)) (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg i) _)
          have h2 : (∑' i : ℕ, (i:ℝ)^(-(1+σ))) ≤ 1 + 1/σ := by
            have hh := Commons.Analysis.PSeries.tsum_nat_rpow_neg_le (p := 1+σ) (by linarith)
            rw [show (1:ℝ) + σ - 1 = σ by ring] at hh
            simpa [one_div] using hh
          linarith
      _ = x^σ * (1 + 1/σ) * (1/(T * Real.log 2)) := by ring
  have hP2eq : (∑ i ∈ range (N2 - N1), a (i + (N1+1))) = ∑ n ∈ Icc (N1+1) N2, a n := by
    rw [← Finset.Ico_add_one_right_eq_Icc (N1+1) N2, Finset.sum_Ico_eq_sum_range]
    rw [show (N2 + 1) - (N1 + 1) = N2 - N1 by omega]
    apply Finset.sum_congr rfl
    intro k hk
    rw [add_comm]
  have hP2 : (∑ i ∈ range (N2 - N1), a (i + (N1+1))) ≤ (4/x) * (100 * (x * Real.log x / T) + 100) := by
    rw [hP2eq]
    have hmiddle := Commons.NumberTheory.Zeta.middle_min_dist_sum_le x T hx hT
    have hmiddle' : (∑ n ∈ Icc (N1+1) N2, min 1 ((2*x)/(T*|x - (n:ℝ)|)))
        ≤ 100 * (x * Real.log x / T) + 100 := by
      rw [← hN1, ← hN2] at hmiddle
      exact hmiddle
    have hx4 : 0 ≤ 4/x := by positivity
    calc (∑ n ∈ Icc (N1+1) N2, a n)
        ≤ ∑ n ∈ Icc (N1+1) N2, (4/x) * min 1 ((2*x)/(T*|x - (n:ℝ)|)) := by
          apply Finset.sum_le_sum
          intro n hn
          have hn1 : x/2 < (n:ℝ) := by
            have hge : N1 + 1 ≤ n := (Finset.mem_Icc.mp hn).1
            have hcast : ((N1+1:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast hge
            have hfloor : x/2 < (N1:ℝ) + 1 := by rw [hN1]; exact Nat.lt_floor_add_one (x/2)
            rw [Nat.cast_add, Nat.cast_one] at hcast
            linarith
          have hn2 : (n:ℝ) ≤ 2*x := by
            have hle : n ≤ N2 := (Finset.mem_Icc.mp hn).2
            have hcast : (n:ℝ) ≤ (N2:ℝ) := by exact_mod_cast hle
            have hfloor : (N2:ℝ) ≤ 2*x := by rw [hN2]; exact Nat.floor_le (by linarith : (0:ℝ) ≤ 2*x)
            linarith
          exact perron_central_term_le x σ T hx hσ hσ1 hT0 hn1 hn2
      _ = (4/x) * ∑ n ∈ Icc (N1+1) N2, min 1 ((2*x)/(T*|x - (n:ℝ)|)) := by rw [Finset.mul_sum]
      _ ≤ (4/x) * (100 * (x * Real.log x / T) + 100) :=
          mul_le_mul_of_nonneg_left hmiddle' hx4
  have hP3 : (∑' i, a (i + (N2+1))) ≤ x^σ * (1 + 1/σ) * (1/(T * Real.log 2)) := by
    have hpt : ∀ i, a (i + (N2+1))
        ≤ x^σ * ((i + (N2+1):ℕ):ℝ)^(-(1+σ)) * (1/(T*Real.log 2)) := by
      intro i
      apply perron_right_term_le x σ T hx hσ hT0
      have hfloor : 2*x < (N2:ℝ) + 1 := by rw [hN2]; exact Nat.lt_floor_add_one (2*x)
      have hcast : ((N2+1:ℕ):ℝ) ≤ ((i + (N2+1):ℕ):ℝ) := Nat.cast_le.mpr (by omega)
      push_cast at hfloor hcast ⊢
      linarith
    have hs1 : Summable (fun i => ((i + (N2+1):ℕ):ℝ)^(-(1+σ))) :=
      (summable_nat_add_iff (N2+1)).mpr hsp
    have hrhs : Summable (fun i => x^σ * ((i + (N2+1):ℕ):ℝ)^(-(1+σ)) * (1/(T*Real.log 2))) := by
      have := hs1.mul_left (x^σ * (1/(T*Real.log 2)))
      simpa only [mul_assoc, mul_comm, mul_left_comm] using this
    have hlhs : Summable (fun i => a (i + (N2+1))) := (summable_nat_add_iff (N2+1)).mpr ha
    have hle : (∑' i, a (i + (N2+1)))
        ≤ ∑' i, x^σ * ((i + (N2+1):ℕ):ℝ)^(-(1+σ)) * (1/(T*Real.log 2)) :=
      Summable.tsum_le_tsum hpt hlhs hrhs
    have heq : (∑' i, x^σ * ((i + (N2+1):ℕ):ℝ)^(-(1+σ)) * (1/(T*Real.log 2)))
        = x^σ * (1/(T*Real.log 2)) * ∑' i, ((i + (N2+1):ℕ):ℝ)^(-(1+σ)) := by
      rw [show (∑' i, x^σ * ((i + (N2+1):ℕ):ℝ)^(-(1+σ)) * (1/(T*Real.log 2)))
            = ∑' i, (x^σ * (1/(T*Real.log 2))) * ((i + (N2+1):ℕ):ℝ)^(-(1+σ)) by
          apply tsum_congr; intro i; ring]
      rw [tsum_mul_left]
    have hshift_le : (∑' i, ((i + (N2+1):ℕ):ℝ)^(-(1+σ))) ≤ 1 + 1/σ := by
      have hbase : Summable (fun i : ℕ => ((i + 1:ℕ):ℝ)^(-(1+σ))) := (summable_nat_add_iff 1).mpr hsp
      have hle1 : (∑' i, ((i + (N2+1):ℕ):ℝ)^(-(1+σ))) ≤ ∑' i, ((i + 1:ℕ):ℝ)^(-(1+σ)) := by
        apply Summable.tsum_le_tsum
        · intro i
          apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
          push_cast
          have : (1:ℕ) ≤ N2 := by omega
          have : (1:ℝ) ≤ (N2:ℝ) := by exact_mod_cast ‹(1:ℕ) ≤ N2›
          linarith
        · exact hs1
        · exact hbase
      have heq1 : (∑' i : ℕ, ((i + 1:ℕ):ℝ)^(-(1+σ))) = ∑' i : ℕ, (i:ℝ)^(-(1+σ)) := by
        have h := hsp.sum_add_tsum_nat_add 1
        have h0 : ((0:ℕ):ℝ)^(-(1+σ)) = 0 := by
          rw [Nat.cast_zero, Real.zero_rpow (show (-(1+σ) : ℝ) ≠ 0 by linarith)]
        simp only [Finset.sum_range_one] at h
        rw [h0, zero_add] at h
        simpa only [Nat.cast_add, Nat.cast_one] using h
      have hbound : (∑' i : ℕ, (i:ℝ)^(-(1+σ))) ≤ 1 + 1/σ := by
        have hh := Commons.Analysis.PSeries.tsum_nat_rpow_neg_le (p := 1+σ) (by linarith)
        rw [show (1:ℝ) + σ - 1 = σ by ring] at hh
        simpa [one_div] using hh
      linarith
    have hc3_nn : 0 ≤ x^σ * (1/(T*Real.log 2)) := by positivity
    calc (∑' i, a (i + (N2+1)))
        ≤ ∑' i, x^σ * ((i + (N2+1):ℕ):ℝ)^(-(1+σ)) * (1/(T*Real.log 2)) := hle
      _ = x^σ * (1/(T*Real.log 2)) * ∑' i, ((i + (N2+1):ℕ):ℝ)^(-(1+σ)) := heq
      _ ≤ x^σ * (1/(T*Real.log 2)) * (1 + 1/σ) := mul_le_mul_of_nonneg_left hshift_le hc3_nn
      _ = x^σ * (1 + 1/σ) * (1/(T * Real.log 2)) := by ring
  have hSbound : (∑' n, a n)
      ≤ x^σ*(1+1/σ)*(1/(T*Real.log 2)) + (4/x)*(100*(x*Real.log x/T)+100)
        + x^σ*(1+1/σ)*(1/(T*Real.log 2)) := by
    rw [hS]
    linarith [hP1, hP2, hP3]
  have hlog2half : (1:ℝ)/2 ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h
    linarith
  have hlogx_le : Real.log x ≤ x^σ / σ :=
    Commons.Analysis.ExpLog.log_le_rpow_div (by linarith : (1:ℝ) ≤ x) hσ
  have hQ1 : (1:ℝ) ≤ x^σ * (1 + 1/σ) + 1 := by
    have hxσ1 : (1:ℝ) ≤ x^σ := Real.one_le_rpow (by linarith : (1:ℝ) ≤ x) (le_of_lt hσ)
    have hb : 0 ≤ 1 + 1/σ := by positivity
    have : 0 ≤ x^σ * (1+1/σ) := mul_nonneg (le_trans zero_le_one hxσ1) hb
    linarith
  have hxσ_nn : 0 ≤ x^σ := Real.rpow_nonneg hx0 σ
  have hb_nn : 0 ≤ 1 + 1/σ := by positivity
  have hA : x^σ*(1+1/σ)*(1/(T*Real.log 2)) ≤ 2 * (x^σ*(1+1/σ))/T := by
    have hlog : 1/(T*Real.log 2) ≤ 2/T := by
      rw [div_le_div_iff₀ (by positivity : 0 < T*Real.log 2) (by linarith : 0 < T)]
      nlinarith
    have hc : 0 ≤ x^σ*(1+1/σ) := mul_nonneg hxσ_nn hb_nn
    calc x^σ*(1+1/σ)*(1/(T*Real.log 2)) = (x^σ*(1+1/σ)) * (1/(T*Real.log 2)) := by ring
      _ ≤ (x^σ*(1+1/σ)) * (2/T) := mul_le_mul_of_nonneg_left hlog hc
      _ = 2 * (x^σ*(1+1/σ))/T := by ring
  have hB : (4/x)*(100*(x*Real.log x/T)+100) ≤ 800 * (x^σ*(1+1/σ)+1)/T := by
    have hAσ : x^σ * (1/σ) ≤ x^σ * (1+1/σ) := by
      apply mul_le_mul_of_nonneg_left _ hxσ_nn; linarith
    have hlogx : Real.log x ≤ x^σ * (1+1/σ) := by
      have hEq : x^σ / σ = x^σ * (1/σ) := by ring
      rw [hEq] at hlogx_le
      exact le_trans hlogx_le hAσ
    have h1 : 400 * Real.log x / T ≤ 400 * (x^σ*(1+1/σ))/T := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hT0)
      linarith
    have h2 : 400/x ≤ 400/T := div_le_div_of_nonneg_left (by norm_num) hT0 hTle
    have h3 : (400:ℝ)/T ≤ 400 * (x^σ*(1+1/σ)+1)/T := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hT0)
      nlinarith [hQ1]
    have h4 : 400 * (x^σ*(1+1/σ))/T ≤ 400 * (x^σ*(1+1/σ)+1)/T := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hT0)
      linarith
    have hsq : 400 * Real.log x / T ≤ 400 * (x^σ*(1+1/σ)+1)/T := le_trans h1 h4
    have hpx : 400/x ≤ 400 * (x^σ*(1+1/σ)+1)/T := le_trans h2 h3
    have hexp : (4/x)*(100*(x*Real.log x/T)+100) = 400 * Real.log x / T + 400/x := by
      field_simp; ring
    rw [hexp]
    calc 400 * Real.log x / T + 400/x
        ≤ 400 * (x^σ*(1+1/σ)+1)/T + 400 * (x^σ*(1+1/σ)+1)/T := add_le_add hsq hpx
      _ = 800 * (x^σ*(1+1/σ)+1)/T := by ring
  have hfin : x^σ*(1+1/σ)*(1/(T*Real.log 2)) + (4/x)*(100*(x*Real.log x/T)+100)
        + x^σ*(1+1/σ)*(1/(T*Real.log 2)) ≤ 1000 * (x^σ * (1 + 1/σ) + 1)/T := by
    have h4 : 4 * (x^σ*(1+1/σ))/T ≤ 4 * (x^σ*(1+1/σ)+1)/T := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hT0)
      linarith
    have hA2 : 2 * (x^σ*(1+1/σ)*(1/(T*Real.log 2))) ≤ 4 * (x^σ*(1+1/σ)+1)/T := by
      calc 2 * (x^σ*(1+1/σ)*(1/(T*Real.log 2)))
          ≤ 2 * (2 * (x^σ*(1+1/σ))/T) := mul_le_mul_of_nonneg_left hA (by norm_num)
        _ = 4 * (x^σ*(1+1/σ))/T := by ring
        _ ≤ 4 * (x^σ*(1+1/σ)+1)/T := h4
    have h804 : 4 * (x^σ*(1+1/σ)+1)/T + 800 * (x^σ*(1+1/σ)+1)/T
        ≤ 1000 * (x^σ*(1+1/σ)+1)/T := by
      rw [show 4 * (x^σ*(1+1/σ)+1)/T + 800 * (x^σ*(1+1/σ)+1)/T
            = 804 * (x^σ*(1+1/σ)+1)/T by ring]
      apply div_le_div_of_nonneg_right _ (le_of_lt hT0)
      have : (0:ℝ) ≤ x^σ*(1+1/σ)+1 := by linarith [hQ1]
      nlinarith
    have e : x^σ*(1+1/σ)*(1/(T*Real.log 2)) + (4/x)*(100*(x*Real.log x/T)+100)
        + x^σ*(1+1/σ)*(1/(T*Real.log 2))
        = 2 * (x^σ*(1+1/σ)*(1/(T*Real.log 2))) + (4/x)*(100*(x*Real.log x/T)+100) := by ring
    rw [e]
    calc 2 * (x^σ*(1+1/σ)*(1/(T*Real.log 2))) + (4/x)*(100*(x*Real.log x/T)+100)
        ≤ 4 * (x^σ*(1+1/σ)+1)/T + 800 * (x^σ*(1+1/σ)+1)/T := add_le_add hA2 hB
      _ ≤ 1000 * (x^σ*(1+1/σ)+1)/T := h804
  calc (∑' n, a n) ≤ x^σ*(1+1/σ)*(1/(T*Real.log 2)) + (4/x)*(100*(x*Real.log x/T)+100)
        + x^σ*(1+1/σ)*(1/(T*Real.log 2)) := hSbound
    _ ≤ 1000 * (x^σ*(1+1/σ)+1)/T := hfin

end

end Commons.NumberTheory.Moebius
