import Mathlib
import Submission.Commons.NumberTheory.Zeta.chebyshevPsi_sub_id_rh_bound
import Submission.Commons.NumberTheory.Mertens.theta_sub_id_phi_integrableOn_Ioi
import Submission.Commons.Analysis.Real.tail_integral_log10

open MeasureTheory Set Filter intervalIntegral
open scoped Topology

namespace Commons.Analysis.Real

/-- `t ^ (3/2) = t * sqrt t` for `t > 0`. -/
private lemma rpow_three_halves_eq_mul_sqrt {t : ℝ} (ht : 0 < t) :
    t ^ (3 / 2 : ℝ) = t * Real.sqrt t := by
  rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add ht,
      Real.rpow_one]

/-- `t ^ (3/2) = (sqrt t) ^ 3` for `t > 0`. -/
private lemma rpow_three_halves_eq_sqrt_pow {t : ℝ} (ht : 0 < t) :
    t ^ (3 / 2 : ℝ) = (Real.sqrt t) ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (t ^ (1 / 2 : ℝ)) 3, ← Real.rpow_mul (le_of_lt ht)]
  congr 1
  norm_num

/-- `t ^ 2 = (sqrt t) ^ 4` for `t > 0`. -/
private lemma sq_eq_sqrt_pow_four {t : ℝ} (ht : 0 < t) :
    t ^ 2 = (Real.sqrt t) ^ 4 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (t ^ (1 / 2 : ℝ)) 4, ← Real.rpow_mul (le_of_lt ht),
      ← Real.rpow_natCast t 2]
  congr 1
  norm_num

/-- Tail bound for the ninth power: `∫_{Ioi x} (log t)^9 / t^(3/2) ≤ K (log x)^9 / sqrt x`. -/
private theorem tail_integral_log9 :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, Real.exp 1 ≤ x →
      (∫ t in Set.Ioi x, (Real.log t) ^ 9 / t ^ (3 / 2 : ℝ)) ≤
        K * (Real.log x) ^ 9 / Real.sqrt x := by
  obtain ⟨K, hKpos, hK⟩ := Commons.Analysis.Real.tail_integral_log10
  refine ⟨K, hKpos, ?_⟩
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hx1 : 1 < x := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hx
  have hlogx1 : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at h
  have hlogx0 : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hlogx1
  have h9int : IntegrableOn (fun t : ℝ => (Real.log t) ^ 9 / t ^ (3 / 2 : ℝ)) (Set.Ioi x) :=
    Commons.NumberTheory.Mertens.integrableOn_Ioi_log_pow_div_rpow (n := 9) (s := (3 / 2 : ℝ))
      (c := x) (by norm_num) (le_of_lt hx1)
  have h10int : IntegrableOn (fun t : ℝ => (Real.log t) ^ 10 / t ^ (3 / 2 : ℝ)) (Set.Ioi x) :=
    Commons.NumberTheory.Mertens.integrableOn_Ioi_log_pow_div_rpow (n := 10) (s := (3 / 2 : ℝ))
      (c := x) (by norm_num) (le_of_lt hx1)
  have hpoint : ∀ t ∈ Set.Ioi x,
      (Real.log t) ^ 9 / t ^ (3 / 2 : ℝ) ≤
        ((Real.log t) ^ 10 / t ^ (3 / 2 : ℝ)) / Real.log x := by
    intro t ht
    have hxt : x < t := ht
    have ht1 : 1 < t := lt_trans hx1 hxt
    have ht0 : 0 < t := lt_trans zero_lt_one ht1
    have hlogt0 : 0 < Real.log t := Real.log_pos ht1
    have hlogxt : Real.log x ≤ Real.log t := Real.log_le_log hx0 (le_of_lt hxt)
    have htp : 0 < t ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos ht0 _
    rw [div_div, div_le_div_iff₀ htp (mul_pos htp hlogx0)]
    have key : (Real.log t) ^ 9 * Real.log x ≤ (Real.log t) ^ 10 := by
      calc (Real.log t) ^ 9 * Real.log x ≤ (Real.log t) ^ 9 * Real.log t :=
            mul_le_mul_of_nonneg_left hlogxt (pow_nonneg hlogt0.le 9)
        _ = (Real.log t) ^ 10 := by ring
    calc (Real.log t) ^ 9 * (t ^ (3 / 2 : ℝ) * Real.log x)
        = ((Real.log t) ^ 9 * Real.log x) * t ^ (3 / 2 : ℝ) := by ring
      _ ≤ (Real.log t) ^ 10 * t ^ (3 / 2 : ℝ) := mul_le_mul_of_nonneg_right key htp.le
  have hle : (fun t : ℝ => (Real.log t) ^ 9 / t ^ (3 / 2 : ℝ)) ≤ᵐ[volume.restrict (Set.Ioi x)]
      (fun t : ℝ => ((Real.log t) ^ 10 / t ^ (3 / 2 : ℝ)) / Real.log x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hpoint t ht
  have hcollapse : (∫ t in Set.Ioi x, ((Real.log t) ^ 10 / t ^ (3 / 2 : ℝ)) / Real.log x)
      = (Real.log x)⁻¹ * (∫ t in Set.Ioi x, (Real.log t) ^ 10 / t ^ (3 / 2 : ℝ)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    dsimp only
    rw [div_eq_inv_mul]
  have hmono : (∫ t in Set.Ioi x, (Real.log t) ^ 9 / t ^ (3 / 2 : ℝ)) ≤
      (Real.log x)⁻¹ * (∫ t in Set.Ioi x, (Real.log t) ^ 10 / t ^ (3 / 2 : ℝ)) := by
    have h1 := integral_mono_ae h9int (h10int.div_const (Real.log x)) hle
    rwa [hcollapse] at h1
  have hconv : (∫ t in Set.Ioi x, (Real.log t) ^ 10 / t ^ (3 / 2 : ℝ)) =
      (∫ t in Set.Ioi x, (Real.log t) ^ 10 / (t * Real.sqrt t)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := lt_trans hx0 ht
    dsimp only
    rw [rpow_three_halves_eq_mul_sqrt ht0]
  rw [hconv] at hmono
  have hpow : (Real.log x)⁻¹ * (Real.log x) ^ 10 = (Real.log x) ^ 9 := by
    rw [show (Real.log x) ^ 10 = Real.log x * (Real.log x) ^ 9 by ring, ← mul_assoc,
        inv_mul_cancel₀ hlogx0.ne', one_mul]
  calc (∫ t in Set.Ioi x, (Real.log t) ^ 9 / t ^ (3 / 2 : ℝ))
      ≤ (Real.log x)⁻¹ * (∫ t in Set.Ioi x, (Real.log t) ^ 10 / (t * Real.sqrt t)) := hmono
    _ ≤ (Real.log x)⁻¹ * (K * (Real.log x) ^ 10 / Real.sqrt x) :=
          mul_le_mul_of_nonneg_left (hK x hx) (inv_nonneg.mpr hlogx0.le)
    _ = K * (Real.log x) ^ 9 / Real.sqrt x := by
          calc (Real.log x)⁻¹ * (K * (Real.log x) ^ 10 / Real.sqrt x)
              = K * ((Real.log x)⁻¹ * (Real.log x) ^ 10) / Real.sqrt x := by ring
            _ = K * (Real.log x) ^ 9 / Real.sqrt x := by rw [hpow]

theorem integral_Ioi_chebyshevPsi_sub_id_mul_psiKfun_bound (h : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      |∫ t in Set.Ioi Y, ((Chebyshev.psi t : ℝ) - t) *
          ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))| ≤
        C * (Real.log Y) ^ 9 / Y ^ (1 / 2 : ℝ) := by
  obtain ⟨C₁, hC₁pos, y₀, hψ⟩ := Commons.NumberTheory.Zeta.chebyshevPsi_sub_id_rh_bound h
  obtain ⟨K, hKpos, hK⟩ := tail_integral_log9
  refine ⟨2 * C₁ * K, by positivity, max y₀ (Real.exp 1), ?_⟩
  intro Y hY
  have hYy₀ : y₀ ≤ Y := le_trans (le_max_left _ _) hY
  have hYe : Real.exp 1 ≤ Y := le_trans (le_max_right _ _) hY
  have hY1 : 1 < Y := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) hYe
  set F : ℝ → ℝ := fun t => (Chebyshev.psi t - t) *
      ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) with hF
  set G : ℝ → ℝ := fun t => 2 * C₁ * ((Real.log t) ^ 9 / t ^ (3 / 2 : ℝ)) with hG
  have hbase_int : IntegrableOn (fun t : ℝ => (Real.log t) ^ 9 / t ^ (3 / 2 : ℝ)) (Set.Ioi Y) :=
    Commons.NumberTheory.Mertens.integrableOn_Ioi_log_pow_div_rpow (n := 9) (s := (3 / 2 : ℝ))
      (c := Y) (by norm_num) (le_of_lt hY1)
  have hGint : IntegrableOn G (Set.Ioi Y) := by
    rw [hG]
    exact hbase_int.const_mul (2 * C₁)
  have hGnn : ∀ t ∈ Set.Ioi Y, 0 ≤ G t := by
    intro t ht
    have ht1 : 1 < t := lt_trans hY1 ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht1
    have hlogt0 : 0 < Real.log t := Real.log_pos ht1
    have h1 : 0 < (Real.log t) ^ 9 := pow_pos hlogt0 9
    have h2 : 0 < t ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos ht0 _
    have h3 : 0 < (Real.log t) ^ 9 / t ^ (3 / 2 : ℝ) := div_pos h1 h2
    have h4 : 0 < 2 * C₁ := by positivity
    rw [hG]
    exact le_of_lt (mul_pos h4 h3)
  have hleF : ∀ t ∈ Set.Ioi Y, ‖F t‖ ≤ G t := by
    intro t ht
    have hYt : Y < t := ht
    have ht_y₀ : y₀ ≤ t := le_trans hYy₀ (le_of_lt hYt)
    have ht_e : Real.exp 1 ≤ t := le_trans hYe (le_of_lt hYt)
    have ht1 : 1 < t := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by norm_num)) ht_e
    have ht0 : 0 < t := lt_trans zero_lt_one ht1
    have hlogt1 : 1 ≤ Real.log t := by
      have hh := Real.log_le_log (Real.exp_pos 1) ht_e
      rwa [Real.log_exp] at hh
    have hlogt0 : 0 < Real.log t := lt_of_lt_of_le zero_lt_one hlogt1
    have hKnn : 0 ≤ (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2) := by positivity
    have hnorm : ‖F t‖ = |Chebyshev.psi t - t| *
        ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by
      rw [hF]
      simp only
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hKnn]
    rw [hnorm, hG]
    have hψt := hψ t ht_y₀
    have halg : (C₁ * Real.sqrt t * (Real.log t) ^ 10) *
        ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) =
        C₁ * ((Real.log t) ^ 9 + (Real.log t) ^ 8) / t ^ (3 / 2 : ℝ) := by
      rw [sq_eq_sqrt_pow_four ht0, rpow_three_halves_eq_sqrt_pow ht0]
      field_simp
    calc |Chebyshev.psi t - t| * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
        ≤ (C₁ * Real.sqrt t * (Real.log t) ^ 10) *
            ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) :=
          mul_le_mul_of_nonneg_right hψt hKnn
      _ = C₁ * ((Real.log t) ^ 9 + (Real.log t) ^ 8) / t ^ (3 / 2 : ℝ) := halg
      _ ≤ 2 * C₁ * ((Real.log t) ^ 9 / t ^ (3 / 2 : ℝ)) := by
          have h8 : (Real.log t) ^ 8 ≤ (Real.log t) ^ 9 :=
            pow_le_pow_right₀ hlogt1 (by norm_num)
          have htp : 0 < t ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos ht0 _
          have hstep : ((Real.log t) ^ 9 + (Real.log t) ^ 8) / t ^ (3 / 2 : ℝ)
              ≤ 2 * (Real.log t) ^ 9 / t ^ (3 / 2 : ℝ) := by
            apply div_le_div_of_nonneg_right _ htp.le
            linarith
          calc C₁ * ((Real.log t) ^ 9 + (Real.log t) ^ 8) / t ^ (3 / 2 : ℝ)
              = C₁ * (((Real.log t) ^ 9 + (Real.log t) ^ 8) / t ^ (3 / 2 : ℝ)) := by
                rw [mul_div_assoc]
            _ ≤ C₁ * (2 * (Real.log t) ^ 9 / t ^ (3 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_left hstep (le_of_lt hC₁pos)
            _ = 2 * C₁ * ((Real.log t) ^ 9 / t ^ (3 / 2 : ℝ)) := by ring
  have hFmeas : AEStronglyMeasurable F (volume.restrict (Set.Ioi Y)) := by
    have hm : Measurable F := by
      rw [hF]
      exact ((Chebyshev.psi_mono.measurable.sub measurable_id).mul
        ((Real.measurable_log.add_const 1).div
          ((measurable_id.pow_const 2).mul (Real.measurable_log.pow_const 2))))
    exact hm.aestronglyMeasurable
  have hFint : IntegrableOn F (Set.Ioi Y) := by
    refine Integrable.mono hGint hFmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have h1 : ‖F t‖ ≤ G t := hleF t ht
    have h2 : 0 ≤ G t := hGnn t ht
    rw [Real.norm_of_nonneg h2]
    exact h1
  have hle : (fun t => ‖F t‖) ≤ᵐ[volume.restrict (Set.Ioi Y)] G := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hleF t ht
  have hmain : |∫ t in Set.Ioi Y, F t| ≤ 2 * C₁ * (K * (Real.log Y) ^ 9 / Real.sqrt Y) := by
    rw [← Real.norm_eq_abs]
    calc ‖∫ t in Set.Ioi Y, F t‖
        ≤ ∫ t in Set.Ioi Y, ‖F t‖ := norm_integral_le_integral_norm F
      _ ≤ ∫ t in Set.Ioi Y, G t := integral_mono_ae hFint.norm hGint hle
      _ = 2 * C₁ * ∫ t in Set.Ioi Y, (Real.log t) ^ 9 / t ^ (3 / 2 : ℝ) := by
            rw [hG, MeasureTheory.integral_const_mul]
      _ ≤ 2 * C₁ * (K * (Real.log Y) ^ 9 / Real.sqrt Y) :=
            mul_le_mul_of_nonneg_left (hK Y hYe) (by positivity)
  calc |∫ t in Set.Ioi Y, ((Chebyshev.psi t : ℝ) - t) *
          ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))|
      = |∫ t in Set.Ioi Y, F t| := by rw [hF]
    _ ≤ 2 * C₁ * (K * (Real.log Y) ^ 9 / Real.sqrt Y) := hmain
    _ = (2 * C₁ * K) * (Real.log Y) ^ 9 / Y ^ (1 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow]
          ring

end Commons.Analysis.Real
