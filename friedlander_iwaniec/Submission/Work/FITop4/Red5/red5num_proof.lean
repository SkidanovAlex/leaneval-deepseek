import Mathlib
import Submission.Work.FITop4.Red5.window_setup
import Submission.Work.FITop4.Numeric4.numHyp_proof2

set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace Work.FITop4.Red5

open Filter
open scoped Topology

noncomputable section

/-! ## Numeric facts about the round-5 constants -/

lemma bFun_nonneg (η : ℝ) : 0 ≤ bFun η := by
  unfold bFun
  have h1 : 0 < (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 4) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h2 : 0 < (2 : ℝ) ^ (η⁻¹ * Real.log η⁻¹ + 1) :=
    Real.rpow_pos_of_pos (by norm_num) _
  linarith

lemma BmaxBig_ge_pow31 (η : ℝ) : (2 : ℝ) ^ (31 : ℕ) ≤ BmaxBig η := by
  unfold BmaxBig; linarith [bFun_nonneg η]

lemma BmaxBig_pos (η : ℝ) : 0 < BmaxBig η := by
  have h := BmaxBig_ge_pow31 η
  have : (0 : ℝ) < (2 : ℝ) ^ (31 : ℕ) := by norm_num
  linarith

lemma Asave_ge_one : (1 : ℝ) ≤ Asave := by unfold Asave; norm_num
lemma Asave_nonneg : (0 : ℝ) ≤ Asave := by unfold Asave; norm_num
lemma Aprime_Asave_nonneg : (0 : ℝ) ≤ Aprime Asave := by unfold Aprime Asave; norm_num
lemma Aprime_Asave_ge_one : (1 : ℝ) ≤ Aprime Asave := by unfold Aprime Asave; norm_num
lemma Aprime_Asave_sq_nonneg : (0 : ℝ) ≤ (Aprime Asave) ^ 2 := sq_nonneg _
lemma Asave_le_eight_Aprime : Asave ≤ 8 * Aprime Asave := by unfold Asave Aprime; norm_num
lemma Asave_add_Aprime_le_pow31 : Asave + Aprime Asave ≤ (2 : ℝ) ^ (31 : ℕ) := by
  unfold Asave Aprime; norm_num
lemma Asave_add_Aprime_le_BmaxBig (η : ℝ) : Asave + Aprime Asave ≤ BmaxBig η :=
  le_trans Asave_add_Aprime_le_pow31 (BmaxBig_ge_pow31 η)
lemma Asave_le_BmaxBig (η : ℝ) : Asave ≤ BmaxBig η :=
  le_trans (le_add_of_nonneg_right Aprime_Asave_nonneg) (Asave_add_Aprime_le_BmaxBig η)
lemma Asave_Aprime_sum_nonneg : (0 : ℝ) ≤ Asave + Aprime Asave :=
  add_nonneg Asave_nonneg Aprime_Asave_nonneg

/-! ## The threshold -/

lemma red5num_threshold (η : ℝ) (hη0 : 0 < η) :
    ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
      64 ≤ x ∧ 4 ≤ Real.log (x : ℝ) ∧ 8 ≤ Real.log (x : ℝ) ∧
      Asave + Aprime Asave ≤ Real.log (Real.log (x : ℝ)) ∧
      8 * Aprime Asave * Real.log (Real.log (x : ℝ)) ≤ Real.log (x : ℝ) ∧
      Aprime Asave * Real.log (Real.log (x : ℝ)) ≤ (η / 3) * Real.log (x : ℝ) := by
  have hx64 : ∀ᶠ x : ℕ in atTop, 64 ≤ x :=
    Filter.eventually_atTop.2 ⟨64, fun b hb => hb⟩
  have hL4 : ∀ᶠ x : ℕ in atTop, (4 : ℝ) ≤ Real.log (x : ℝ) :=
    Numeric4.ev_const_le_log 4 (by norm_num)
  have hL8 : ∀ᶠ x : ℕ in atTop, (8 : ℝ) ≤ Real.log (x : ℝ) :=
    Numeric4.ev_const_le_log 8 (by norm_num)
  have hLL : ∀ᶠ x : ℕ in atTop,
      Asave + Aprime Asave ≤ Real.log (Real.log (x : ℝ)) :=
    Numeric4.ev_const_le_loglog _ Asave_Aprime_sum_nonneg
  have hD1 : ∀ᶠ x : ℕ in atTop,
      8 * Aprime Asave * Real.log (Real.log (x : ℝ)) ≤ Real.log (x : ℝ) := by
    have hthr : ∀ᶠ x : ℕ in atTop,
        256 * (Aprime Asave) ^ 2 ≤ Real.log (x : ℝ) :=
      Numeric4.ev_const_le_log (256 * (Aprime Asave) ^ 2)
        (mul_nonneg (by norm_num) Aprime_Asave_sq_nonneg)
    filter_upwards [hthr] with x hx
    have hLnn : 0 ≤ Real.log (x : ℝ) := by
      have : 0 ≤ 256 * (Aprime Asave) ^ 2 :=
        mul_nonneg (by norm_num) Aprime_Asave_sq_nonneg
      linarith
    have hs : 0 ≤ Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_nonneg _
    have hlog := Real.log_le_rpow_div hLnn (by norm_num : (0 : ℝ) < 1 / 2)
    rw [Real.rpow_div_two_eq_sqrt _ hLnn, Real.rpow_one,
        show Real.sqrt (Real.log (x : ℝ)) / (1 / 2) = 2 * Real.sqrt (Real.log (x : ℝ)) by
          ring] at hlog
    have hsqrt_ge : 16 * Aprime Asave ≤ Real.sqrt (Real.log (x : ℝ)) := by
      rw [← Real.sqrt_sq (mul_nonneg (by norm_num) Aprime_Asave_nonneg)]
      apply Real.sqrt_le_sqrt
      have h2 : (16 * Aprime Asave) ^ 2 = 256 * (Aprime Asave) ^ 2 := by ring
      rw [h2]; exact hx
    have h1 : 8 * Aprime Asave * Real.log (Real.log (x : ℝ))
        ≤ 8 * Aprime Asave * (2 * Real.sqrt (Real.log (x : ℝ))) :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg (by norm_num) Aprime_Asave_nonneg)
    have h3 : (16 : ℝ) * Aprime Asave * Real.sqrt (Real.log (x : ℝ))
        ≤ Real.sqrt (Real.log (x : ℝ)) * Real.sqrt (Real.log (x : ℝ)) :=
      mul_le_mul_of_nonneg_right hsqrt_ge hs
    have h4 : Real.sqrt (Real.log (x : ℝ)) * Real.sqrt (Real.log (x : ℝ))
        = Real.log (x : ℝ) := by
      rw [← pow_two]; exact Real.sq_sqrt hLnn
    nlinarith [h1, h3, h4]
  have hD2 : ∀ᶠ x : ℕ in atTop,
      Aprime Asave * Real.log (Real.log (x : ℝ)) ≤ (η / 3) * Real.log (x : ℝ) := by
    have hthr : ∀ᶠ x : ℕ in atTop,
        36 * (Aprime Asave) ^ 2 / η ^ 2 ≤ Real.log (x : ℝ) :=
      Numeric4.ev_const_le_log (36 * (Aprime Asave) ^ 2 / η ^ 2)
        (div_nonneg (mul_nonneg (by norm_num) Aprime_Asave_sq_nonneg)
          (by positivity))
    filter_upwards [hthr] with x hx
    have hLnn : 0 ≤ Real.log (x : ℝ) := by
      have h0 : 0 ≤ 36 * (Aprime Asave) ^ 2 / η ^ 2 :=
        div_nonneg (mul_nonneg (by norm_num) Aprime_Asave_sq_nonneg) (by positivity)
      linarith
    have hs : 0 ≤ Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_nonneg _
    have hlog := Real.log_le_rpow_div hLnn (by norm_num : (0 : ℝ) < 1 / 2)
    rw [Real.rpow_div_two_eq_sqrt _ hLnn, Real.rpow_one,
        show Real.sqrt (Real.log (x : ℝ)) / (1 / 2) = 2 * Real.sqrt (Real.log (x : ℝ)) by
          ring] at hlog
    have hsqrt_ge : 6 * Aprime Asave / η ≤ Real.sqrt (Real.log (x : ℝ)) := by
      rw [← Real.sqrt_sq (div_nonneg
        (mul_nonneg (by norm_num) Aprime_Asave_nonneg) (le_of_lt hη0))]
      apply Real.sqrt_le_sqrt
      have h2 : (6 * Aprime Asave / η) ^ 2 = 36 * (Aprime Asave) ^ 2 / η ^ 2 := by ring
      rw [h2]; exact hx
    have h1 : Aprime Asave * Real.log (Real.log (x : ℝ))
        ≤ Aprime Asave * (2 * Real.sqrt (Real.log (x : ℝ))) :=
      mul_le_mul_of_nonneg_left hlog Aprime_Asave_nonneg
    have h3 : (6 * Aprime Asave / η) * Real.sqrt (Real.log (x : ℝ))
        ≤ Real.sqrt (Real.log (x : ℝ)) * Real.sqrt (Real.log (x : ℝ)) :=
      mul_le_mul_of_nonneg_right hsqrt_ge hs
    have h4 : Real.sqrt (Real.log (x : ℝ)) * Real.sqrt (Real.log (x : ℝ))
        = Real.log (x : ℝ) := by
      rw [← pow_two]; exact Real.sq_sqrt hLnn
    have h3' : 6 * Aprime Asave / η * Real.sqrt (Real.log (x : ℝ)) ≤ Real.log (x : ℝ) :=
      le_trans h3 (le_of_eq h4)
    have h8 : (η / 3) * (6 * Aprime Asave / η * Real.sqrt (Real.log (x : ℝ)))
        ≤ (η / 3) * Real.log (x : ℝ) :=
      mul_le_mul_of_nonneg_left h3' (by positivity)
    have h6 : Aprime Asave * (2 * Real.sqrt (Real.log (x : ℝ)))
        = 2 * Aprime Asave * Real.sqrt (Real.log (x : ℝ)) := by ring
    have h7 : (η / 3) * (6 * Aprime Asave / η * Real.sqrt (Real.log (x : ℝ)))
        = 2 * Aprime Asave * Real.sqrt (Real.log (x : ℝ)) := by
      field_simp; ring
    rw [h6, ← h7] at h1
    exact le_trans h1 h8
  have hall := hx64.and (hL4.and (hL8.and (hLL.and (hD1.and hD2))))
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hall
  exact ⟨x₀, hx₀⟩

/-! ## The main theorem -/

end
end Work.FITop4.Red5
