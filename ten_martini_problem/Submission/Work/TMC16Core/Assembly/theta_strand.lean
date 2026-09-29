import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Core.pd_window_helpers
import Submission.Work.TMC16Core.Main.theta_refold

namespace Work.TMC16Core.Assembly

open Work.TMC16Core

set_option maxHeartbeats 2000000

theorem theta_strand_fast_aux {α θ : ℝ} {K₀ : ℤ} {csm : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hK₀1 : 1 ≤ K₀) (hcsm : 0 < csm) (hcsm1 : csm ≤ 1 / 2)
    (h1 : ∀ k : ℤ, |k| < K₀ → csm ≤ Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α))
    (h2 : ∀ k : ℤ, K₀ ≤ |k| →
      ((((k.natAbs : ℕ) : ℝ))⁻¹) ^ 2 ≤ Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α))
    (hqpos : ∀ i, 0 < q i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ)))
    {n : ℕ} {B : ℤ} (hB : 1 ≤ B)
    (hBle : (B : ℝ) ≤ 1000 * (Real.rpow (q (n + 1) : ℝ) (8 / 9 : ℝ) + (q n : ℝ)))
    (hfast : (100000 / csm * ((q n : ℝ) + 1)) ^ 9 ≤ (q (n + 1) : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
      Real.log (1 / c) ≤ Real.log 2 + Real.log (1 / csm) + 2 * Real.log ((q n : ℝ) + 2) ∧
      ∀ j : ℤ, |(j : ℝ)| ≤ (B : ℝ) → c ≤ Work.TMC16Core.fracDist (2 * θ + (j : ℝ) * α) := by
  have hqn_pos : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hqpos n
  have hqn_ge1 : (1 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hqpos n
  have hqp1_pos : (0 : ℝ) < (q (n + 1) : ℝ) := by exact_mod_cast hqpos (n + 1)
  have hqn1_pos : (0 : ℝ) < (q n : ℝ) + 1 := by linarith
  have hqn1_ge : (1 : ℝ) ≤ (q n : ℝ) + 1 := by linarith
  have hMn_pos : (0 : ℝ) < 100000 / csm := by positivity
  have hroot : (100000 / csm) * ((q n : ℝ) + 1) ≤ Real.rpow (q (n + 1) : ℝ) (1 / 9 : ℝ) := by
    have hbase : (0 : ℝ) ≤ (100000 / csm) * ((q n : ℝ) + 1) := le_of_lt (by positivity)
    have hstep := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ ((100000 / csm) * ((q n : ℝ) + 1)) ^ 9)
      hfast (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 9)
    have heq : (((100000 / csm) * ((q n : ℝ) + 1)) ^ 9) ^ (1 / 9 : ℝ)
        = (100000 / csm) * ((q n : ℝ) + 1) := by
      rw [show (1 / 9 : ℝ) = (((9 : ℕ) : ℝ))⁻¹ by norm_num]
      exact Real.pow_rpow_inv_natCast hbase (by norm_num)
    rwa [heq] at hstep
  have hsplit : Real.rpow (q (n + 1) : ℝ) (8 / 9 : ℝ)
      = (q (n + 1) : ℝ) / Real.rpow (q (n + 1) : ℝ) (1 / 9 : ℝ) := by
    have h9 : 0 < Real.rpow (q (n + 1) : ℝ) (1 / 9 : ℝ) := Real.rpow_pos_of_pos hqp1_pos _
    rw [eq_div_iff (ne_of_gt h9)]
    have h := Real.rpow_add hqp1_pos (1 / 9 : ℝ) (8 / 9 : ℝ)
    rw [show (1 / 9 : ℝ) + 8 / 9 = 1 by norm_num, Real.rpow_one] at h
    rw [mul_comm]
    exact h.symm
  have hF2 : (100000 / csm) * ((q n : ℝ) + 1) ≤ (q (n + 1) : ℝ) := by
    have hMn_ge1 : (1 : ℝ) ≤ 100000 / csm := by rw [le_div_iff₀ hcsm]; nlinarith [hcsm1]
    have hge1 : (1 : ℝ) ≤ (100000 / csm) * ((q n : ℝ) + 1) := by nlinarith [hMn_ge1, hqn1_ge]
    have h2' : (100000 / csm) * ((q n : ℝ) + 1)
        ≤ ((100000 / csm) * ((q n : ℝ) + 1)) ^ 9 := by
      have := pow_le_pow_right₀ hge1 (by norm_num : 1 ≤ 9)
      simpa using this
    exact le_trans h2' hfast
  set c₀ : ℝ := min csm (4 / ((q n : ℝ)) ^ 2) with hc₀
  have hc₀pos : 0 < c₀ := by rw [hc₀]; exact lt_min hcsm (by positivity)
  have hc₀le : c₀ ≤ 1 / 2 := by rw [hc₀]; exact le_trans (min_le_left _ _) hcsm1
  have hc₀le_csm : c₀ ≤ csm := by rw [hc₀]; exact min_le_left _ _
  have hc₀le_sq : c₀ ≤ 4 / ((q n : ℝ)) ^ 2 := by rw [hc₀]; exact min_le_right _ _
  refine ⟨c₀ / 2, by positivity, by linarith, ?_, ?_⟩
  · have hc₀_inv : 1 / c₀ ≤ ((q n : ℝ)) ^ 2 / csm := by
      rw [hc₀]
      rcases le_total csm (4 / ((q n : ℝ)) ^ 2) with h | h
      · rw [min_eq_left h, ← sub_nonneg]
        field_simp
        nlinarith [hcsm, hqn_ge1]
      · rw [min_eq_right h, one_div, inv_div, ← sub_nonneg]
        field_simp
        nlinarith [hcsm, hcsm1, hqn_ge1]
    have h1' : 1 / (c₀ / 2) ≤ 2 * (((q n : ℝ)) ^ 2 / csm) := by
      have heq : 1 / (c₀ / 2) = 2 * (1 / c₀) := by rw [one_div, inv_div]; ring
      rw [heq]; linarith [hc₀_inv]
    have h2' : Real.log (1 / (c₀ / 2)) ≤ Real.log (2 * (((q n : ℝ)) ^ 2 / csm)) :=
      Real.log_le_log (by positivity) h1'
    have h3 : Real.log (2 * (((q n : ℝ)) ^ 2 / csm))
        = Real.log 2 + 2 * Real.log ((q n : ℝ)) + Real.log (1 / csm) := by
      rw [Real.log_mul (by norm_num) (by positivity),
        Real.log_div (by positivity) (ne_of_gt hcsm), Real.log_pow]
      rw [one_div, Real.log_inv]; ring
    rw [h3] at h2'
    have h4 : Real.log ((q n : ℝ)) ≤ Real.log ((q n : ℝ) + 2) :=
      Real.log_le_log hqn_pos (by linarith)
    linarith [h2', h4]
  · intro j hj
    refine Main.theta_refold (Q := q n) (Δ := Δ n) (c := c₀) (Y := (B : ℝ))
      (hqpos n) hc₀pos (hΔeq n) ?_ ?_ j hj
    · intro r hr
      by_cases hlt : |r| < K₀
      · exact le_trans hc₀le_csm (h1 r hlt)
      · push Not at hlt
        have h2r := h2 r hlt
        have hcast : (((r.natAbs : ℕ) : ℝ)) = |(r : ℝ)| := by
          rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
        rw [hcast] at h2r
        have hrge1 : (1 : ℝ) ≤ |(r : ℝ)| := by
          have h1' : (1 : ℤ) ≤ |r| := le_trans hK₀1 hlt
          have hR : (1 : ℝ) ≤ ((|r| : ℤ) : ℝ) := by exact_mod_cast h1'
          rwa [Int.cast_abs] at hR
        have hrpos : 0 < |(r : ℝ)| := by linarith
        have hrleR : |(r : ℝ)| ≤ (q n : ℝ) / 2 := by
          rw [← Int.cast_abs]; exact_mod_cast hr
        have hmid : c₀ ≤ ((|(r : ℝ)|)⁻¹) ^ 2 := by
          refine le_trans hc₀le_sq ?_
          have hr2 : ((|(r : ℝ)|)) ^ 2 ≤ ((q n : ℝ) / 2) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hrleR 2
          rw [inv_pow]
          rw [show (4 : ℝ) / ((q n : ℝ)) ^ 2 = (((q n : ℝ)) ^ 2 / 4)⁻¹ by rw [inv_div]]
          rw [inv_le_inv₀ (by positivity) (by positivity)]
          nlinarith [hr2]
        exact le_trans hmid h2r
    · have hΔnn : 0 ≤ Δ n := by rw [hΔeq n]; exact abs_nonneg _
      have hΔlt : Δ n < 1 / (q (n + 1) : ℝ) := hΔup n
      have hfacpos : 0 < (B : ℝ) / (q n : ℝ) + 1 / 2 := by
        have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
        have : 0 < (B : ℝ) / (q n : ℝ) := div_pos (by linarith) hqn_pos
        linarith
      have hstep1 : ((B : ℝ) / (q n : ℝ) + 1 / 2) * Δ n
          ≤ ((B : ℝ) / (q n : ℝ) + 1 / 2) * (1 / (q (n + 1) : ℝ)) :=
        mul_le_mul_of_nonneg_left (le_of_lt hΔlt) (le_of_lt hfacpos)
      have hBq : (B : ℝ) / (q n : ℝ)
          ≤ 1000 * (Real.rpow (q (n + 1) : ℝ) (8 / 9 : ℝ) + (q n : ℝ)) / (q n : ℝ) :=
        div_le_div_of_nonneg_right hBle (le_of_lt hqn_pos)
      have hstep2 : (B : ℝ) / (q n : ℝ) + 1 / 2
          ≤ (1000 * (Real.rpow (q (n + 1) : ℝ) (8 / 9 : ℝ) + (q n : ℝ)) / (q n : ℝ)) + 1 / 2 := by
        linarith
      have hstep3 : ((B : ℝ) / (q n : ℝ) + 1 / 2) * (1 / (q (n + 1) : ℝ))
          ≤ (1000 * (Real.rpow (q (n + 1) : ℝ) (8 / 9 : ℝ) + (q n : ℝ)) / (q n : ℝ) + 1 / 2)
            * (1 / (q (n + 1) : ℝ)) :=
        mul_le_mul_of_nonneg_right hstep2 (by positivity)
      have hrw : (1000 * (Real.rpow (q (n + 1) : ℝ) (8 / 9 : ℝ) + (q n : ℝ)) / (q n : ℝ) + 1 / 2)
            * (1 / (q (n + 1) : ℝ))
          = 1000 / ((q n : ℝ) * Real.rpow (q (n + 1) : ℝ) (1 / 9 : ℝ)) + 1000 / (q (n + 1) : ℝ)
            + 1 / (2 * (q (n + 1) : ℝ)) := by
        rw [hsplit]
        field_simp; try ring
      have hchain : ((B : ℝ) / (q n : ℝ) + 1 / 2) * Δ n
          ≤ 1000 / ((q n : ℝ) * Real.rpow (q (n + 1) : ℝ) (1 / 9 : ℝ)) + 1000 / (q (n + 1) : ℝ)
            + 1 / (2 * (q (n + 1) : ℝ)) := by
        rw [← hrw]; exact le_trans hstep1 hstep3
      have hkey : (4000 : ℝ) * ((q n : ℝ)) ^ 2
          ≤ ((100000 / csm) * ((q n : ℝ) + 1)) ^ 9 := by
        rw [mul_pow]
        have hM9 : (4000 : ℝ) ≤ (100000 / csm) ^ 9 := by
          have h1 : (4000 : ℝ) ≤ 100000 / csm := by rw [le_div_iff₀ hcsm]; nlinarith [hcsm1]
          have hge : (1 : ℝ) ≤ 100000 / csm := by rw [le_div_iff₀ hcsm]; nlinarith [hcsm1]
          exact le_trans h1 (by simpa using (pow_le_pow_right₀ hge (by norm_num : (1 : ℕ) ≤ 9)))
        have hq9 : ((q n : ℝ)) ^ 2 ≤ ((q n : ℝ) + 1) ^ 9 := by
          have h1 : ((q n : ℝ)) ^ 2 ≤ ((q n : ℝ) + 1) ^ 2 := by nlinarith [hqn_pos]
          exact le_trans h1 (pow_le_pow_right₀ hqn1_ge (by norm_num : (2 : ℕ) ≤ 9))
        have hmul : (4000 : ℝ) * ((q n : ℝ)) ^ 2
            ≤ (100000 / csm) ^ 9 * ((q n : ℝ) + 1) ^ 9 :=
          mul_le_mul hM9 hq9 (by positivity) (by positivity)
        exact hmul
      have hT1mid : 1000 / ((q n : ℝ) * Real.rpow (q (n + 1) : ℝ) (1 / 9 : ℝ))
          ≤ csm / (100 * (q n : ℝ) * ((q n : ℝ) + 1)) := by
        have h1' : 1000 / ((q n : ℝ) * Real.rpow (q (n + 1) : ℝ) (1 / 9 : ℝ))
            ≤ 1000 / ((q n : ℝ) * ((100000 / csm) * ((q n : ℝ) + 1))) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity)
            (mul_le_mul_of_nonneg_left hroot (le_of_lt hqn_pos))
        have h2' : 1000 / ((q n : ℝ) * ((100000 / csm) * ((q n : ℝ) + 1)))
            = csm / (100 * (q n : ℝ) * ((q n : ℝ) + 1)) := by
          field_simp; ring
        linarith [h1', le_of_eq h2']
      have hT1 : 1000 / ((q n : ℝ) * Real.rpow (q (n + 1) : ℝ) (1 / 9 : ℝ))
          ≤ csm / (100 * ((q n : ℝ) + 1)) := by
        refine le_trans hT1mid ?_
        apply div_le_div_of_nonneg_left (le_of_lt hcsm) (by positivity)
        nlinarith [hqn_ge1]
      have hS1 : 1000 / ((q n : ℝ) * Real.rpow (q (n + 1) : ℝ) (1 / 9 : ℝ))
          ≤ (1 / 2) / (100 * ((q n : ℝ)) ^ 2) := by
        have ha : csm / (100 * (q n : ℝ) * ((q n : ℝ) + 1))
            ≤ (1 / 2) / (100 * (q n : ℝ) * ((q n : ℝ) + 1)) :=
          div_le_div_of_nonneg_right hcsm1 (by positivity)
        have hb : (1 / 2) / (100 * (q n : ℝ) * ((q n : ℝ) + 1))
            ≤ (1 / 2) / (100 * ((q n : ℝ)) ^ 2) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          nlinarith [hqn_ge1]
        exact le_trans hT1mid (le_trans ha hb)
      have hT2 : 1000 / (q (n + 1) : ℝ) ≤ csm / (100 * ((q n : ℝ) + 1)) := by
        have heq : csm / (100 * ((q n : ℝ) + 1)) = 1000 / ((100000 / csm) * ((q n : ℝ) + 1)) := by
          field_simp; ring
        rw [heq]
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hF2
      have hS2 : 1000 / (q (n + 1) : ℝ) ≤ 1000 / (4000 * ((q n : ℝ)) ^ 2) := by
        have h1' : 1000 / (q (n + 1) : ℝ)
            ≤ 1000 / (((100000 / csm) * ((q n : ℝ) + 1)) ^ 9) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hfast
        have h2' : 1000 / (((100000 / csm) * ((q n : ℝ) + 1)) ^ 9)
            ≤ 1000 / (4000 * ((q n : ℝ)) ^ 2) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hkey
        linarith [h1', h2']
      have hT3 : 1 / (2 * (q (n + 1) : ℝ)) ≤ csm / (200000 * ((q n : ℝ) + 1)) := by
        have heq : csm / (200000 * ((q n : ℝ) + 1))
            = 1 / (2 * ((100000 / csm) * ((q n : ℝ) + 1))) := by
          field_simp; ring
        rw [heq]
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith [hF2])
      have hS3 : 1 / (2 * (q (n + 1) : ℝ)) ≤ 1 / (8000 * ((q n : ℝ)) ^ 2) := by
        have h1' : 1 / (2 * (q (n + 1) : ℝ))
            ≤ 1 / (2 * (((100000 / csm) * ((q n : ℝ) + 1)) ^ 9)) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith [hfast])
        have h2' : (8000 : ℝ) * ((q n : ℝ)) ^ 2
            ≤ 2 * (((100000 / csm) * ((q n : ℝ) + 1)) ^ 9) := by linarith [hkey]
        have h3' : 1 / (2 * (((100000 / csm) * ((q n : ℝ) + 1)) ^ 9))
            ≤ 1 / (8000 * ((q n : ℝ)) ^ 2) :=
          one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 8000 * ((q n : ℝ)) ^ 2) h2'
        linarith [h1', h3']
      rw [hc₀]
      rcases le_total csm (4 / ((q n : ℝ)) ^ 2) with hh | hh
      · rw [min_eq_left hh]
        have e1 : csm / (100 * ((q n : ℝ) + 1)) ≤ csm / 100 :=
          div_le_div_of_nonneg_left (le_of_lt hcsm) (by norm_num) (by nlinarith [hqn1_ge])
        have e2 : csm / (200000 * ((q n : ℝ) + 1)) ≤ csm / 200000 :=
          div_le_div_of_nonneg_left (le_of_lt hcsm) (by norm_num) (by nlinarith [hqn1_ge])
        linarith [hchain, hT1, hT2, hT3, e1, e2]
      · rw [min_eq_right hh]
        have hsum : ((B : ℝ) / (q n : ℝ) + 1 / 2) * Δ n
            ≤ (1 / 2) / (100 * ((q n : ℝ)) ^ 2) + 1000 / (4000 * ((q n : ℝ)) ^ 2)
              + 1 / (8000 * ((q n : ℝ)) ^ 2) := by
          linarith [hchain, hS1, hS2, hS3]
        have harith : (1 / 2) / (100 * ((q n : ℝ)) ^ 2) + 1000 / (4000 * ((q n : ℝ)) ^ 2)
              + 1 / (8000 * ((q n : ℝ)) ^ 2) ≤ 4 / ((q n : ℝ)) ^ 2 / 2 := by
          rw [← sub_nonneg]
          field_simp
          nlinarith [hqn_pos]
        linarith [hsum, harith]

theorem theta_strand_slow_aux {α θ : ℝ} {K₀ : ℤ} {csm : ℝ} {q : ℕ → ℕ}
    (hK₀1 : 1 ≤ K₀) (hcsm : 0 < csm) (hcsm1 : csm ≤ 1 / 2)
    (h1 : ∀ k : ℤ, |k| < K₀ → csm ≤ Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α))
    (h2 : ∀ k : ℤ, K₀ ≤ |k| →
      ((((k.natAbs : ℕ) : ℝ))⁻¹) ^ 2 ≤ Work.TMC16Core.fracDist (2 * θ + (k : ℝ) * α))
    (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    {n : ℕ} {B : ℤ} (hB : 1 ≤ B)
    (hBle : (B : ℝ) ≤ 1000 * (Real.rpow (q (n + 1) : ℝ) (8 / 9 : ℝ) + (q n : ℝ)))
    (hslow : (q (n + 1) : ℝ) ≤ (100000 / csm * ((q n : ℝ) + 1)) ^ 9) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
      Real.log (1 / c) ≤ Real.log 2 + Real.log (1 / csm) + 2 * Real.log 2001
        + 18 * Real.log (100000 / csm) + 18 * Real.log ((q n : ℝ) + 2) ∧
      ∀ j : ℤ, |(j : ℝ)| ≤ (B : ℝ) → c ≤ Work.TMC16Core.fracDist (2 * θ + (j : ℝ) * α) := by
  have hB1 : (0 : ℝ) < (B : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    linarith
  have hBge1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have hqn_pos : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hqpos n
  have hqn1_ge : (1 : ℝ) ≤ (q n : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hqpos n
    linarith
  refine ⟨min csm (1 / ((B : ℝ) + 1) ^ 2), lt_min hcsm (by positivity), ?_, ?_, ?_⟩
  · exact le_trans (min_le_left _ _) hcsm1
  · have hc_inv : 1 / min csm (1 / ((B : ℝ) + 1) ^ 2) ≤ (1 / csm) * ((B : ℝ) + 1) ^ 2 := by
      rcases le_total csm (1 / ((B : ℝ) + 1) ^ 2) with h | h
      · rw [min_eq_left h]
        have h1' : (1 : ℝ) ≤ ((B : ℝ) + 1) ^ 2 := by nlinarith [hBge1]
        calc 1 / csm = (1 / csm) * 1 := by ring
          _ ≤ (1 / csm) * ((B : ℝ) + 1) ^ 2 :=
              mul_le_mul_of_nonneg_left h1' (by positivity)
      · rw [min_eq_right h, one_div, one_div, inv_inv]
        have h1' : (1 : ℝ) ≤ 1 / csm := by rw [le_div_iff₀ hcsm]; linarith
        calc ((B : ℝ) + 1) ^ 2 = 1 * ((B : ℝ) + 1) ^ 2 := by ring
          _ ≤ (1 / csm) * ((B : ℝ) + 1) ^ 2 :=
              mul_le_mul_of_nonneg_right h1' (by positivity)
    have hlog1 : Real.log (1 / min csm (1 / ((B : ℝ) + 1) ^ 2))
        ≤ Real.log (1 / csm) + 2 * Real.log ((B : ℝ) + 1) := by
      have hpos : 0 < 1 / min csm (1 / ((B : ℝ) + 1) ^ 2) := by positivity
      calc Real.log (1 / min csm (1 / ((B : ℝ) + 1) ^ 2))
          ≤ Real.log ((1 / csm) * ((B : ℝ) + 1) ^ 2) := Real.log_le_log hpos hc_inv
        _ = Real.log (1 / csm) + Real.log (((B : ℝ) + 1) ^ 2) := by
              rw [Real.log_mul (by positivity) (by positivity)]
        _ = Real.log (1 / csm) + 2 * Real.log ((B : ℝ) + 1) := by
              rw [Real.log_pow]; ring
    have hBle2 : (B : ℝ) + 1 ≤ 2001 * (((100000 / csm) * ((q n : ℝ) + 1)) ^ 9) := by
      have hqp_ge1 : (1 : ℝ) ≤ (q (n + 1) : ℝ) := by exact_mod_cast hqpos (n + 1)
      have hqrle : Real.rpow (q (n + 1) : ℝ) (8 / 9 : ℝ) ≤ (q (n + 1) : ℝ) :=
        Real.rpow_le_self_of_one_le hqp_ge1 (by norm_num)
      have hqn_le : (q n : ℝ) ≤ (q (n + 1) : ℝ) := by
        have := hmono (Nat.lt_succ_self n)
        exact_mod_cast le_of_lt this
      have hB2 : (B : ℝ) ≤ 2000 * (q (n + 1) : ℝ) := by
        calc (B : ℝ) ≤ 1000 * (Real.rpow (q (n + 1) : ℝ) (8 / 9 : ℝ) + (q n : ℝ)) := hBle
          _ ≤ 1000 * ((q (n + 1) : ℝ) + (q (n + 1) : ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              linarith
          _ = 2000 * (q (n + 1) : ℝ) := by ring
      nlinarith [hB2, hqp_ge1]
    have hlogB : 2 * Real.log ((B : ℝ) + 1)
        ≤ 2 * Real.log 2001 + 18 * Real.log (100000 / csm) + 18 * Real.log ((q n : ℝ) + 2) := by
      have h1' := Real.log_le_log hB1 hBle2
      have h2 : Real.log (2001 * (((100000 / csm) * ((q n : ℝ) + 1)) ^ 9))
          = Real.log 2001 + 9 * Real.log ((100000 / csm) * ((q n : ℝ) + 1)) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        ring
      have h3 : Real.log ((100000 / csm) * ((q n : ℝ) + 1))
          = Real.log (100000 / csm) + Real.log ((q n : ℝ) + 1) :=
        Real.log_mul (by positivity) (by positivity)
      have h4 : Real.log ((q n : ℝ) + 1) ≤ Real.log ((q n : ℝ) + 2) := by
        apply Real.log_le_log (by linarith); linarith
      rw [h2, h3] at h1'
      linarith
    have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith [hlog1, hlogB, hlog2nn]
  · intro j hj
    rcases lt_or_ge (|j|) K₀ with hlt | hge
    · exact le_trans (min_le_left _ _) (h1 j hlt)
    · have h2j := h2 j hge
      have hcast : (((j.natAbs : ℕ) : ℝ)) = |(j : ℝ)| := by
        rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
      rw [hcast] at h2j
      have hjge1 : (1 : ℝ) ≤ |(j : ℝ)| := by
        have h1' : (1 : ℤ) ≤ |j| := le_trans hK₀1 hge
        have hR : (1 : ℝ) ≤ ((|j| : ℤ) : ℝ) := by exact_mod_cast h1'
        rwa [Int.cast_abs] at hR
      have hjpos : 0 < |(j : ℝ)| := by linarith
      have hle : 1 / ((B : ℝ) + 1) ^ 2 ≤ ((|(j : ℝ)|)⁻¹) ^ 2 := by
        have hsq : ((|(j : ℝ)|)) ^ 2 ≤ ((B : ℝ) + 1) ^ 2 := by nlinarith [hj, hBge1]
        rw [one_div, inv_pow]
        rw [inv_le_inv₀ (by positivity : (0 : ℝ) < ((B : ℝ) + 1) ^ 2) (pow_pos hjpos 2)]
        nlinarith [hsq]
      exact le_trans (min_le_right _ _) (le_trans hle h2j)


theorem theta_strand {α θ : ℝ} (hθ : θ ∉ Work.TMC16Core.Theta α)
    {q : ℕ → ℕ} {Δ : ℕ → ℝ} (hqpos : ∀ i, 0 < q i) (hmono : StrictMono q)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ))) :
    ∃ Cθ : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ B : ℤ, 1 ≤ B →
      (B : ℝ) ≤ 1000 * (Real.rpow (q (n + 1) : ℝ) (8 / 9 : ℝ) + (q n : ℝ)) →
      ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧
        Real.log (1 / c) ≤ Cθ + 20 * Real.log ((q n : ℝ) + 2) ∧
        ∀ j : ℤ, |(j : ℝ)| ≤ (B : ℝ) → c ≤ Work.TMC16Core.fracDist (2 * θ + (j : ℝ) * α) := by
  obtain ⟨K₀, hK₀1, csm, hcsm, hcsm1, h1, h2⟩ := Core.theta_setup hθ
  refine ⟨Real.log 2 + Real.log (1 / csm) + 2 * Real.log 2001
            + 18 * Real.log (100000 / csm) + 18, 0, ?_⟩
  intro n _ B hB hBle
  rcases le_or_gt ((q (n + 1) : ℝ)) ((100000 / csm * ((q n : ℝ) + 1)) ^ 9) with hslow | hfast
  · obtain ⟨c, hc0, hc1, hlog, hrange⟩ :=
      theta_strand_slow_aux hK₀1 hcsm hcsm1 h1 h2 hqpos hmono hB hBle hslow
    refine ⟨c, hc0, hc1, ?_, hrange⟩
    have hlog0 : 0 ≤ Real.log ((q n : ℝ) + 2) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hqpos n
      linarith
    linarith
  · obtain ⟨c, hc0, hc1, hlog, hrange⟩ :=
      theta_strand_fast_aux hK₀1 hcsm hcsm1 h1 h2 hqpos hΔeq hΔup hB hBle hfast.le
    refine ⟨c, hc0, hc1, ?_, hrange⟩
    have hM1 : (1 : ℝ) ≤ 100000 / csm := by
      rw [le_div_iff₀ hcsm]; nlinarith
    have hlogM : 0 ≤ Real.log (100000 / csm) := Real.log_nonneg hM1
    have h2001 : 0 ≤ Real.log 2001 := Real.log_nonneg (by norm_num)
    have hlog0 : 0 ≤ Real.log ((q n : ℝ) + 2) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ (q n : ℝ) := by exact_mod_cast hqpos n
      linarith
    linarith

end Work.TMC16Core.Assembly
