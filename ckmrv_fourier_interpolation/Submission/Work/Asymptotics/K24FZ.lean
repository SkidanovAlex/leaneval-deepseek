/-
# The `z`-atoms at the threshold `Im z ≥ 3`, and the uniform divisor bound

Continues `Submission/Work/Asymptotics/K24FBase.lean`.
-/
import Mathlib
import Submission.Work.Asymptotics.K24FBase
import Submission.Work.Asymptotics.Compact.zsmall
import Submission.Work.Asymptotics.cusp_E6E2S_div_E4_second
import Submission.Work.Asymptotics.E4Fun_far_imagAxis_near_one
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.Asymptotics.DeltaFun_funnel_lower_sharp
import Submission.Work.FunnelNumerics.E4_funnel_bounds

set_option maxHeartbeats 1000000

namespace Work.Asymptotics

open UpperHalfPlane
open Work.Kernels

noncomputable section

namespace K24F

/-! ## 4. The `z`-atoms at the threshold `Im z ≥ 3` -/

lemma zS0_norm (z : ℍ) (hz : 1 ≤ z.im) : ‖S0 z‖ ≤ 3 := by
  have h := Small.S0c_norm_le z hz
  simpa only [Small.S0c, S0] using h

theorem E4_ne_zero_three (z : ℍ) (hz : 3 ≤ z.im) : E4Fun z ≠ 0 := by
  intro h0
  have h1 := E4Fun_far_imagAxis_near_one z hz
  rw [h0, zero_sub, norm_neg, norm_one] at h1
  norm_num at h1

theorem E4_inv_le_two_three (z : ℍ) (hz : 3 ≤ z.im) : ‖(E4Fun z)⁻¹‖ ≤ 2 := by
  have h1 : (1 / 2 : ℝ) ≤ ‖E4Fun z‖ := Work.FunnelNumerics.E4_funnel_bounds.2 z hz
  have hpos : 0 < ‖E4Fun z‖ := by linarith
  rw [norm_inv, show (2 : ℝ) = (1 / 2)⁻¹ by norm_num]
  exact (inv_le_inv₀ hpos (by norm_num)).mpr h1

/-- `E₆E₂ˢ/E₄ - S₀ + 24q + 744qS₀ = O(q²)` at the threshold `Im z ≥ 3`. -/
theorem E6_E2S_div_E4_second_three :
    Small.IsSmallT 3 (fun z => E6Fun z * E2S z / E4Fun z - Small.S0c z
      + 24 * qParamFun z + 744 * qParamFun z * Small.S0c z) 2 := by
  have hT : (1 : ℝ) ≤ 3 := by norm_num
  have ha : Small.IsSmallT 3 (fun z => E4Fun z - 1) 1 := Small.E4_sub_one.of_le hT
  have hb : Small.IsSmallT 3 (fun z => E6Fun z - 1) 1 := Small.E6_sub_one.of_le hT
  have hs : Small.IsSmallT 3 (fun z => E2S z - Small.S0c z) 1 := Small.E2S_sub_S0c.of_le hT
  have hc0 : Small.IsSmallT 3 Small.S0c 0 := Small.S0c_bounded.of_le hT
  have hinv' : Small.IsSmallT 3 (fun z => (E4Fun z)⁻¹) 0 :=
    ⟨2, by norm_num, fun z hz => by simpa using E4_inv_le_two_three z hz⟩
  have hba : Small.IsSmallT 3 (fun z => (E6Fun z - 1) - (E4Fun z - 1)) 1 := hb.sub hT ha
  have hX : Small.IsSmallT 3
      (fun z => (E2S z - Small.S0c z) + Small.S0c z * ((E6Fun z - 1) - (E4Fun z - 1))
        + (E6Fun z - 1) * (E2S z - Small.S0c z)) 1 := by
    have h1 := (hs.add hT (hc0.mul hT hba))
    have h2 := (hb.mul hT hs).mono hT (by norm_num : 1 ≤ 1 + 1)
    exact (h1.add hT h2).congr (fun z => by ring)
  have hY1 : Small.IsSmallT 3 (fun z => E2Fun z - 1 + 24 * qParamFun z) 2 :=
    Small.E2_sub_one_second.of_le hT
  have hY2 : Small.IsSmallT 3 (fun z => Small.S0c z * ((E6Fun z - 1 + 504 * qParamFun z)
      - (E4Fun z - 1 - 240 * qParamFun z))) 2 :=
    hc0.mul hT ((Small.E6_sub_one_second.of_le hT).sub hT (Small.E4_sub_one_second.of_le hT))
  have hY3 : Small.IsSmallT 3 (fun z => (E6Fun z - 1) * (E2S z - Small.S0c z)) 2 := hb.mul hT hs
  have hY : Small.IsSmallT 3
      (fun z => (E2Fun z - 1 + 24 * qParamFun z)
        + Small.S0c z * ((E6Fun z - 1 + 504 * qParamFun z) - (E4Fun z - 1 - 240 * qParamFun z))
        + (E6Fun z - 1) * (E2S z - Small.S0c z)) (min 2 (min 2 2)) :=
    (hY1.add hT hY2).add hT hY3
  have hY' : Small.IsSmallT 3
      (fun z => (E2Fun z - 1 + 24 * qParamFun z)
        + Small.S0c z * ((E6Fun z - 1 + 504 * qParamFun z) - (E4Fun z - 1 - 240 * qParamFun z))
        + (E6Fun z - 1) * (E2S z - Small.S0c z)) 2 := by
    simpa using hY
  have hZ : Small.IsSmallT 3 (fun z => ((E2S z - Small.S0c z)
      + Small.S0c z * ((E6Fun z - 1) - (E4Fun z - 1))
      + (E6Fun z - 1) * (E2S z - Small.S0c z)) * (E4Fun z - 1) * (E4Fun z)⁻¹) (1 + 1 + 0) :=
    (hX.mul hT ha).mul hT hinv'
  have hZ' : Small.IsSmallT 3 (fun z => ((E2S z - Small.S0c z)
      + Small.S0c z * ((E6Fun z - 1) - (E4Fun z - 1))
      + (E6Fun z - 1) * (E2S z - Small.S0c z)) * (E4Fun z - 1) * (E4Fun z)⁻¹) 2 := by
    simpa using hZ
  have h := hY'.sub hT hZ'
  refine h.congr_of (fun z hz => ?_)
  have hne : E4Fun z ≠ 0 := E4_ne_zero_three z hz
  simp only [TildeFacts.E2S_eq, Small.S0c]
  field_simp
  ring

/-- `E₆E₂ˢ/E₄ - S₀ = O(q)` at the threshold `Im z ≥ 3`. -/
theorem E6_E2S_div_E4_sub_S0c_three :
    Small.IsSmallT 3 (fun z => E6Fun z * E2S z / E4Fun z - Small.S0c z) 1 := by
  obtain ⟨aG2, haG2p, haG2⟩ := E6_E2S_div_E4_second_three
  refine ⟨aG2 + 24 + 744 * 3, by positivity, fun z hz => ?_⟩
  have hqnn : (0:ℝ) ≤ ‖qParamFun z‖ := norm_nonneg _
  have hq1 : ‖qParamFun z‖ ≤ 1 := norm_qParamFun_le_one z (by linarith)
  have hq2 : ‖qParamFun z‖ ^ 2 ≤ ‖qParamFun z‖ := by nlinarith
  have hS0 : ‖Small.S0c z‖ ≤ 3 := Small.S0c_norm_le z (by linarith)
  have h := haG2 z hz
  simp only [pow_one] at h ⊢
  have hsplit : E6Fun z * E2S z / E4Fun z - Small.S0c z
      = (E6Fun z * E2S z / E4Fun z - Small.S0c z + 24 * qParamFun z
          + 744 * qParamFun z * Small.S0c z)
        - (24 * qParamFun z + 744 * qParamFun z * Small.S0c z) := by ring
  rw [hsplit]
  have hb : ‖24 * qParamFun z + 744 * qParamFun z * Small.S0c z‖
      ≤ (24 + 744 * 3) * ‖qParamFun z‖ := by
    calc ‖(24 : ℂ) * qParamFun z + (744 : ℂ) * qParamFun z * Small.S0c z‖
        ≤ ‖(24 : ℂ) * qParamFun z‖ + ‖(744 : ℂ) * qParamFun z * Small.S0c z‖ := norm_add_le _ _
      _ = 24 * ‖qParamFun z‖ + 744 * ‖qParamFun z‖ * ‖Small.S0c z‖ := by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_ofNat]
      _ ≤ 24 * ‖qParamFun z‖ + 744 * ‖qParamFun z‖ * 3 := by
          have := mul_le_mul_of_nonneg_left hS0
            (by positivity : (0:ℝ) ≤ 744 * ‖qParamFun z‖)
          linarith
      _ = (24 + 744 * 3) * ‖qParamFun z‖ := by ring
  calc ‖(E6Fun z * E2S z / E4Fun z - Small.S0c z + 24 * qParamFun z
        + 744 * qParamFun z * Small.S0c z) - (24 * qParamFun z + 744 * qParamFun z * Small.S0c z)‖
      ≤ ‖E6Fun z * E2S z / E4Fun z - Small.S0c z + 24 * qParamFun z
          + 744 * qParamFun z * Small.S0c z‖ + ‖24 * qParamFun z + 744 * qParamFun z * Small.S0c z‖ :=
        norm_sub_le _ _
    _ ≤ aG2 * ‖qParamFun z‖ ^ 2 + (24 + 744 * 3) * ‖qParamFun z‖ := add_le_add h hb
    _ ≤ (aG2 + 24 + 744 * 3) * ‖qParamFun z‖ := by nlinarith [hqnn, hq2]

/-! ## 5. The uniform divisor bound on the funnel -/

/-- **The uniform divisor bound.**  For `τ` in the funnel and `z = i t` with `t ≥ Im τ + 1`,

  `‖Δ(z)·(j τ - j z)‖ ≥ 1/16`. -/
theorem divisor_lower (τ z : ℍ) (t : ℝ) (hτ : Funnel τ) (ht : τ.im + 1 ≤ t)
    (hz : (z : ℂ) = (t : ℂ) * Complex.I) :
    (1 / 16 : ℝ) ≤ ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ := by
  have hzim : z.im = t := im_of_coe_eq_axis hz
  have ht3 : (3 : ℝ) ≤ t := by have := Funnel.im_two hτ; linarith
  have hz3 : (3 : ℝ) ≤ z.im := by rw [hzim]; exact ht3
  have him1 : (1 : ℝ) ≤ τ.im := Funnel.im_one hτ
  have him2 : (2 : ℝ) ≤ τ.im := Funnel.im_two hτ
  have hkey : DeltaFun z * (jInvariantFun τ - jInvariantFun z)
      = DeltaFun z * jInvariantFun τ - E4Fun z ^ 3 := by
    rw [mul_sub, ClassicalFacts.DeltaFun_mul_jInvariantFun z]
  have hE4z : (1 / 2 : ℝ) ≤ ‖E4Fun z‖ := Work.FunnelNumerics.E4_funnel_bounds.2 z hz3
  have hE4z3 : (1 / 8 : ℝ) ≤ ‖E4Fun z ^ 3‖ := by
    rw [norm_pow]
    exact le_trans (by norm_num : (1/8:ℝ) ≤ (1/2:ℝ)^3) (pow_le_pow_left₀ (by norm_num) hE4z 3)
  have hΔz : ‖DeltaFun z‖ ≤ 2 * Real.exp (-(2 * Real.pi * t)) := by
    have h := DeltaFun_upper_sharp z (by rw [hzim]; linarith)
    rwa [hzim] at h
  have hE4t : ‖E4Fun τ‖ ≤ 3 / 2 := Work.FunnelNumerics.E4_funnel_bounds.1 τ hτ
  have hΔlo : (1 / 2) * Real.exp (-(2 * Real.pi * τ.im)) ≤ ‖DeltaFun τ‖ :=
    DeltaFun_funnel_lower_sharp him2
  have hjτ : ‖jInvariantFun τ‖ ≤ 27 / 4 * Real.exp (2 * Real.pi * τ.im) := by
    have hcoe : jInvariantFun τ = E4Fun τ ^ 3 / DeltaFun τ := rfl
    rw [hcoe, norm_div]
    have hE43 : ‖E4Fun τ ^ 3‖ ≤ (3 / 2) ^ 3 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hE4t 3
    have hpos : 0 < ‖DeltaFun τ‖ := lt_of_lt_of_le (by positivity) hΔlo
    calc ‖E4Fun τ ^ 3‖ / ‖DeltaFun τ‖
        ≤ (3 / 2) ^ 3 / ((1 / 2) * Real.exp (-(2 * Real.pi * τ.im))) :=
          div_le_div₀ (by positivity) hE43 (by positivity) hΔlo
      _ = 27 / 4 * Real.exp (2 * Real.pi * τ.im) := by
          rw [div_eq_mul_inv, mul_inv, inv_exp_neg, show ((1 / 2 : ℝ))⁻¹ = 2 by norm_num]
          norm_num
          ring
  have hprod : ‖DeltaFun z * jInvariantFun τ‖
      ≤ (27 / 2) * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    have h1 : ‖DeltaFun z * jInvariantFun τ‖ ≤ (2 * Real.exp (-(2 * Real.pi * t)))
        * (27 / 4 * Real.exp (2 * Real.pi * τ.im)) := by
      rw [norm_mul]
      exact mul_le_mul hΔz hjτ (norm_nonneg _) (by positivity)
    refine le_trans h1 (le_of_eq ?_)
    have hexp : Real.exp (-(2 * Real.pi * (t - τ.im)))
        = Real.exp (-(2 * Real.pi * t)) * Real.exp (2 * Real.pi * τ.im) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp]; ring
  have hstep : Real.exp (-(2 * Real.pi * (t - τ.im))) ≤ Real.exp (-(2 * Real.pi)) := by
    rw [Real.exp_le_exp]
    nlinarith [Real.pi_pos, ht]
  have he108 : (216 : ℝ) ≤ Real.exp (2 * Real.pi) := by
    have h1 : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have h2 : Real.exp 6 ≤ Real.exp (2 * Real.pi) := Real.exp_le_exp.mpr h1
    have h3 : Real.exp 6 = (Real.exp 1) ^ 6 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    have h4 : (2.7 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 :=
      pow_le_pow_left₀ (show (0:ℝ) ≤ 2.7 by norm_num)
        (show (2.7:ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 6
    have h5 : (216 : ℝ) ≤ (2.7 : ℝ) ^ 6 := by norm_num
    rw [h3] at h2
    linarith
  have h108 : Real.exp (-(2 * Real.pi)) ≤ 1 / 216 := by
    have h : (Real.exp (2 * Real.pi))⁻¹ ≤ (216 : ℝ)⁻¹ :=
      (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr he108
    rw [Real.exp_neg, show (1:ℝ)/216 = (216:ℝ)⁻¹ by norm_num]
    exact h
  have hsmall : (27 / 2) * Real.exp (-(2 * Real.pi * (t - τ.im))) ≤ 1 / 16 := by
    calc (27 / 2) * Real.exp (-(2 * Real.pi * (t - τ.im)))
        ≤ (27 / 2) * Real.exp (-(2 * Real.pi)) := mul_le_mul_of_nonneg_left hstep (by norm_num)
      _ ≤ (27 / 2) * (1 / 216) := mul_le_mul_of_nonneg_left h108 (by norm_num)
      _ = 1 / 16 := by norm_num
  have hfinal : ‖DeltaFun z * jInvariantFun τ‖ ≤ 1 / 16 := le_trans hprod hsmall
  calc (1 / 16 : ℝ) = 1 / 8 - 1 / 16 := by norm_num
    _ ≤ ‖E4Fun z ^ 3‖ - ‖DeltaFun z * jInvariantFun τ‖ := by linarith
    _ ≤ ‖E4Fun z ^ 3 - DeltaFun z * jInvariantFun τ‖ := norm_sub_norm_le _ _
    _ = ‖DeltaFun z * jInvariantFun τ - E4Fun z ^ 3‖ := norm_sub_rev _ _
    _ = ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ := by rw [hkey]

/-- The inverse form of the uniform divisor bound. -/
theorem divisor_inv_le (τ z : ℍ) (t : ℝ) (hτ : Funnel τ) (ht : τ.im + 1 ≤ t)
    (hz : (z : ℂ) = (t : ℂ) * Complex.I) :
    ‖(DeltaFun z * (jInvariantFun τ - jInvariantFun z))⁻¹‖ ≤ 16 := by
  have h : (1 / 16 : ℝ) ≤ ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ :=
    divisor_lower τ z t hτ ht hz
  have hpos : 0 < ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ :=
    lt_of_lt_of_le (by norm_num) h
  rw [norm_inv]
  rw [inv_le_comm₀ hpos (by norm_num : (0:ℝ) < 16)]
  have h16 : ((16 : ℝ))⁻¹ = 1 / 16 := by norm_num
  rw [h16]
  exact h

end K24F

end

end Work.Asymptotics
