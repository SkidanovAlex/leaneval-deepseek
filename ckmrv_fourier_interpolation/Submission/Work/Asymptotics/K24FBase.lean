/-
# The `K₊^{(24)}` funnel: cusp identities, atom bounds and the divisor bound

Self-contained base for the funnel tail expansion of `K₊^{(24)}`
(`Submission/Work/Asymptotics/KPlus_funnel_tail_twentyfour.lean`).
-/
import Mathlib
import Submission.Work.Asymptotics.K24FDefs
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.funnel_zAtom_bounds
import Submission.Work.Asymptotics.Compact.zsmall
import Submission.Work.Asymptotics.E4Fun_far_imagAxis_near_one
import Submission.Work.Asymptotics.cusp_E6E2S_div_E4_second
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.Asymptotics.DeltaFun_funnel_lower_sharp
import Submission.Work.FunnelNumerics.E4_funnel_bounds
import Submission.Work.Kernels.ModerateGrowth

set_option maxHeartbeats 1000000

namespace Work.Asymptotics

open UpperHalfPlane
open Work.Kernels

noncomputable section

namespace K24F

/-! ## 1. The contour `z = i t` -/

lemma im_of_coe_eq_axis {z : ℍ} {t : ℝ} (h : (z : ℂ) = (t : ℂ) * Complex.I) : z.im = t :=
  im_of_coe_eq_mul_I h

lemma qnorm_of_im {z : ℍ} {t : ℝ} (h : z.im = t) :
    ‖qParamFun z‖ = Real.exp (-(2 * Real.pi * t)) := by
  rw [norm_qParamFun, h]

lemma exp_mul_qnorm {τ z : ℍ} {t : ℝ} (h : z.im = t) :
    Real.exp (2 * Real.pi * τ.im) * ‖qParamFun z‖
      = Real.exp (-(2 * Real.pi * (t - τ.im))) := by
  rw [qnorm_of_im h, ← Real.exp_add]
  congr 1
  ring

lemma exp_cancel (τ : ℍ) :
    Real.exp (2 * Real.pi * τ.im) * Real.exp (-(2 * Real.pi * τ.im)) = 1 := by
  rw [← Real.exp_add]
  rw [show 2 * Real.pi * τ.im + -(2 * Real.pi * τ.im) = 0 by ring, Real.exp_zero]

lemma exp_neg_two_pi_im_le_one (τ : ℍ) : Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  nlinarith [Real.pi_pos, τ.im_pos]

lemma inv_exp_neg (τ : ℍ) :
    (Real.exp (-(2 * Real.pi * τ.im)))⁻¹ = Real.exp (2 * Real.pi * τ.im) := by
  rw [← Real.exp_neg]
  rw [show -( -(2 * Real.pi * τ.im)) = 2 * Real.pi * τ.im by ring]

lemma inv_half_exp_neg (τ : ℍ) :
    ((1 / 2 : ℝ) * Real.exp (-(2 * Real.pi * τ.im)))⁻¹ = 2 * Real.exp (2 * Real.pi * τ.im) := by
  rw [mul_inv, inv_exp_neg]
  norm_num

/-! ## 2. The exact identities of the cusp expansion -/

theorem Phi_sub_Phiref (τ z : ℍ) (hE4 : E4Fun z ≠ 0) :
    Phi τ z - Phiref τ z
      = 6 * (r0 τ + r2 τ) * ((E4Fun z - 1) - (E2S z ^ 2 - S0 z ^ 2))
        + r1 τ * ((-12 * jInvariantFun τ + 8640) * (E4Fun z - 1)
            + (12 * jInvariantFun τ - 12096) * (E2S z ^ 2 - S0 z ^ 2))
        + 3456 * r1 τ * (E6Fun z * E2S z / E4Fun z - S0 z) := by
  simp only [Phi, Pfun, Pref, Phiref, Vfun, r0, r1, r2, E14Fun]
  field_simp
  ring

theorem Phi_sub_Phiref_expanded (τ z : ℍ) (hE4 : E4Fun z ≠ 0) :
    Phi τ z - Phiref τ z
      = 6 * (r0 τ + r2 τ) * ((E4Fun z - 1) - (E2S z ^ 2 - S0 z ^ 2))
        + R0 τ * (12 * (E2S z ^ 2 - S0 z ^ 2) - 12 * (E4Fun z - 1))
        + r1 τ * (8640 * (E4Fun z - 1) - 12096 * (E2S z ^ 2 - S0 z ^ 2))
        + 3456 * r1 τ * (E6Fun z * E2S z / E4Fun z - S0 z) := by
  rw [Phi_sub_Phiref τ z hE4, ← r1_mul_j τ]
  ring

theorem Phi_sub_Phiref_sub (τ z : ℍ) (hE4 : E4Fun z ≠ 0) :
    Phi τ z - Phiref τ z - qParamFun z * Q1 τ z
      = 6 * (r0 τ + r2 τ)
          * ((E4Fun z - 1 - 240 * qParamFun z)
              - 2 * S0 z * (E2S z - S0 z + 24 * qParamFun z)
              - (E2S z - S0 z + 24 * qParamFun z) ^ 2
              + 48 * qParamFun z * (E2S z - S0 z + 24 * qParamFun z)
              - 576 * qParamFun z ^ 2)
        + r1 τ
          * ((-12 * jInvariantFun τ + 8640) * (E4Fun z - 1 - 240 * qParamFun z)
            + (12 * jInvariantFun τ - 12096)
              * (2 * S0 z * (E2S z - S0 z + 24 * qParamFun z)
                  + (E2S z - S0 z + 24 * qParamFun z) ^ 2
                  - 48 * qParamFun z * (E2S z - S0 z + 24 * qParamFun z)
                  + 576 * qParamFun z ^ 2))
        + 3456 * r1 τ * (E6Fun z * E2S z / E4Fun z - S0 z
            + 24 * qParamFun z + 744 * qParamFun z * S0 z) := by
  simp only [Phi, Pfun, Pref, Phiref, Vfun, Q1, P1, r0, r1, r2, E14Fun]
  field_simp
  ring

/-- The second-order bracket of `Φ - Φref - q·Q⁽¹⁾`. -/
def B2 (z : ℍ) : ℂ :=
  2 * S0 z * (E2S z - S0 z + 24 * qParamFun z)
    + (E2S z - S0 z + 24 * qParamFun z) ^ 2
    - 48 * qParamFun z * (E2S z - S0 z + 24 * qParamFun z)
    + 576 * qParamFun z ^ 2

theorem Phi_sub_Phiref_sub_expanded (τ z : ℍ) (hE4 : E4Fun z ≠ 0) :
    Phi τ z - Phiref τ z - qParamFun z * Q1 τ z
      = 6 * (r0 τ + r2 τ) * ((E4Fun z - 1 - 240 * qParamFun z) - B2 z)
        + R0 τ * (12 * B2 z - 12 * (E4Fun z - 1 - 240 * qParamFun z))
        + r1 τ * (8640 * (E4Fun z - 1 - 240 * qParamFun z) - 12096 * B2 z)
        + 3456 * r1 τ * (E6Fun z * E2S z / E4Fun z - S0 z
            + 24 * qParamFun z + 744 * qParamFun z * S0 z) := by
  rw [Phi_sub_Phiref_sub τ z hE4, ← r1_mul_j τ]
  simp only [B2]
  ring

theorem Sm3_bracket (τ z : ℍ) :
    Sm3 τ z = 3456 * R0 τ * (S0 z * (E4Fun z ^ 3 - 1)
      - (E6Fun z * E2S z / E4Fun z - S0 z)) := by
  simp only [Sm3]
  ring

theorem Sm4_split (τ z : ℍ) :
    Sm4 τ z = 1728 * r0 τ * (E2S z ^ 2 - S0 z ^ 2)
      + 1728 * r2 τ * (E4Fun z - 1)
      + (1728 * r0 τ * S0 z ^ 2 + 1728 * r2 τ) * (1 - E4Fun z ^ 3) := by
  simp only [Sm4, Ufun, Uref]
  ring

theorem Sm5_split (τ z : ℍ) :
    Sm5 τ z = -(DeltaFun z * jInvariantFun τ)
      * (Q1 τ z + 24 * Phiref τ z - Uref τ z + 3456 * R0 τ * S0 z) := by
  simp only [Sm5, Th0]

/-! ## 3. Growth of the `τ`-atoms on the funnel -/

lemma norm_three_I_div_pi : ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 3 / Real.pi := by
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  norm_num

lemma norm_six_I_div_pi : ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 6 / Real.pi := by
  rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  norm_num

/-- `‖φ₀ τ‖ ≤ C scale τ` on the funnel. -/
theorem phi1_bound : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ →
    ‖Compact.phi1 τ‖ ≤ C * scale τ := by
  obtain ⟨C2, hC2, h2⟩ := E2Fun_bound
  have h3 : (0 : ℝ) < 3 / Real.pi := by positivity
  refine ⟨C2 + 3 / Real.pi, by positivity, fun τ hτ => ?_⟩
  have hE := h2 τ (Funnel.im_one hτ)
  have ht : ‖(τ : ℂ)‖ ≤ scale τ := coe_norm_le_scale τ
  have hs1 : (1 : ℝ) ≤ scale τ := one_le_scale τ
  rw [Compact.phi1]
  have hmain : scale τ * C2 + 3 / Real.pi ≤ (C2 + 3 / Real.pi) * scale τ := by
    have h1 : 3 / Real.pi ≤ 3 / Real.pi * scale τ := le_mul_of_one_le_right h3.le hs1
    have e1 : (C2 + 3 / Real.pi) * scale τ = C2 * scale τ + 3 / Real.pi * scale τ := by ring
    have e2 : scale τ * C2 = C2 * scale τ := by ring
    linarith [h1, e1, e2]
  calc ‖(τ : ℂ) * E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)‖
      ≤ ‖(τ : ℂ) * E2Fun τ‖ + ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ := norm_sub_le _ _
    _ = ‖(τ : ℂ)‖ * ‖E2Fun τ‖ + 3 / Real.pi := by rw [norm_mul, norm_three_I_div_pi]
    _ ≤ scale τ * C2 + 3 / Real.pi := by
        have := mul_le_mul ht hE (norm_nonneg _) (scale_pos τ).le
        linarith
    _ ≤ (C2 + 3 / Real.pi) * scale τ := hmain

/-- `‖φ₂ τ‖ ≤ C scale τ` on the funnel. -/
theorem phi2t_bound : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ →
    ‖Compact.phi2t τ‖ ≤ C * scale τ := by
  obtain ⟨C2, hC2, h2⟩ := E2Fun_bound
  refine ⟨C2 ^ 2 + 6 * C2 / Real.pi, by positivity, fun τ hτ => ?_⟩
  have hE := h2 τ (Funnel.im_one hτ)
  have ht : ‖(τ : ℂ)‖ ≤ scale τ := coe_norm_le_scale τ
  have hs1 : (1 : ℝ) ≤ scale τ := one_le_scale τ
  have h6 : (0 : ℝ) < 6 / Real.pi := by positivity
  rw [Compact.phi2t]
  have hmain : scale τ * C2 ^ 2 + (6 / Real.pi) * C2 ≤ (C2 ^ 2 + 6 * C2 / Real.pi) * scale τ := by
    have h1 : C2 ^ 2 ≤ C2 ^ 2 * scale τ := le_mul_of_one_le_right (by positivity) hs1
    have h2' : (6 / Real.pi) * C2 ≤ (6 / Real.pi) * C2 * scale τ :=
      le_mul_of_one_le_right (by positivity) hs1
    have e1 : scale τ * C2 ^ 2 = C2 ^ 2 * scale τ := by ring
    have e2 : (C2 ^ 2 + 6 * C2 / Real.pi) * scale τ
        = C2 ^ 2 * scale τ + (6 / Real.pi) * C2 * scale τ := by ring
    linarith [h1, h2', e1, e2]
  calc ‖(τ : ℂ) * E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ‖
      ≤ ‖(τ : ℂ) * E2Fun τ ^ 2‖ + ‖(6 * Complex.I / (Real.pi : ℂ)) * E2Fun τ‖ :=
        norm_sub_le _ _
    _ = ‖(τ : ℂ)‖ * ‖E2Fun τ‖ ^ 2 + (6 / Real.pi) * ‖E2Fun τ‖ := by
        rw [norm_mul, norm_mul, norm_pow, norm_six_I_div_pi]
    _ ≤ scale τ * C2 ^ 2 + (6 / Real.pi) * C2 := by
        have h22 : ‖E2Fun τ‖ ^ 2 ≤ C2 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hE 2
        have h1 := mul_le_mul ht h22 (by positivity) (scale_pos τ).le
        have h2' := mul_le_mul_of_nonneg_left hE h6.le
        linarith
    _ ≤ (C2 ^ 2 + 6 * C2 / Real.pi) * scale τ := hmain

/-- The `τ`-atom bounds on the funnel: all the atoms are bounded by one constant `C` times
`scale τ` (times `e^{±2π Im τ}` for `j`, `Δ`, `Δ⁻¹`). -/
theorem tau_atom_bounds : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ →
    ‖r0 τ‖ ≤ C * scale τ ∧
    ‖r2 τ‖ ≤ C * scale τ ∧
    ‖R0 τ‖ ≤ C * scale τ ∧
    ‖r1 τ‖ ≤ C * scale τ ∧
    ‖jInvariantFun τ‖ ≤ C * Real.exp (2 * Real.pi * τ.im) ∧
    ‖DeltaFun τ‖ ≤ C ∧
    ‖(DeltaFun τ)⁻¹‖ ≤ C * Real.exp (2 * Real.pi * τ.im) := by
  obtain ⟨C2, hC2, h2⟩ := E2Fun_bound
  obtain ⟨C4, hC4, h4⟩ := E4Fun_bound
  obtain ⟨C6, hC6, h6⟩ := E6Fun_bound
  obtain ⟨C1, hC1, h1⟩ := phi1_bound
  obtain ⟨C2t, hC2t, h2t⟩ := phi2t_bound
  set C : ℝ := 2 + C4 ^ 2 * C6 + C2t * (C4 * C6) + C1 * C4 ^ 3 + 2 * C1 + 2 * C4 ^ 3
    with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hExpand : ∀ s : ℝ, (2 + C4 ^ 2 * C6 + C2t * (C4 * C6) + C1 * C4 ^ 3 + 2 * C1
        + 2 * C4 ^ 3) * s
      = 2 * s + C4 ^ 2 * C6 * s + C2t * (C4 * C6) * s + C1 * C4 ^ 3 * s
        + 2 * C1 * s + 2 * C4 ^ 3 * s := fun s => by ring
  refine ⟨C, hCpos, fun τ hτ => ?_⟩
  have him1 : (1 : ℝ) ≤ τ.im := Funnel.im_one hτ
  have him2 : (2 : ℝ) ≤ τ.im := Funnel.im_two hτ
  have hE4 := h4 τ him1
  have hE6 := h6 τ him1
  have hphi1 := h1 τ hτ
  have hphi2 := h2t τ hτ
  have hts : ‖(τ : ℂ)‖ ≤ scale τ := coe_norm_le_scale τ
  have hs1 : (1 : ℝ) ≤ scale τ := one_le_scale τ
  have hs0 : (0 : ℝ) < scale τ := scale_pos τ
  have hΔup : ‖DeltaFun τ‖ ≤ 2 * Real.exp (-(2 * Real.pi * τ.im)) := DeltaFun_upper_sharp τ him1
  have hΔlo : (1 / 2) * Real.exp (-(2 * Real.pi * τ.im)) ≤ ‖DeltaFun τ‖ :=
    DeltaFun_funnel_lower_sharp him2
  have hexpnn : (0 : ℝ) < Real.exp (2 * Real.pi * τ.im) := Real.exp_pos _
  have hΔinv : ‖(DeltaFun τ)⁻¹‖ ≤ 2 * Real.exp (2 * Real.pi * τ.im) := by
    have hpos : 0 < ‖DeltaFun τ‖ := lt_of_lt_of_le (by positivity) hΔlo
    have h1' : (‖DeltaFun τ‖)⁻¹ ≤ ((1 / 2) * Real.exp (-(2 * Real.pi * τ.im)))⁻¹ :=
      (inv_le_inv₀ hpos (by positivity)).mpr hΔlo
    rw [norm_inv]
    exact le_trans h1' (le_of_eq (inv_half_exp_neg τ))
  have hj : ‖jInvariantFun τ‖ ≤ 2 * C4 ^ 3 * Real.exp (2 * Real.pi * τ.im) := by
    have hcoe : jInvariantFun τ = E4Fun τ ^ 3 / DeltaFun τ := rfl
    rw [hcoe, norm_div]
    have hE43 : ‖E4Fun τ ^ 3‖ ≤ C4 ^ 3 := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hE4 3
    calc ‖E4Fun τ ^ 3‖ / ‖DeltaFun τ‖
        ≤ C4 ^ 3 / ((1 / 2) * Real.exp (-(2 * Real.pi * τ.im))) :=
          div_le_div₀ (by positivity) hE43 (by positivity) hΔlo
      _ = 2 * C4 ^ 3 * Real.exp (2 * Real.pi * τ.im) := by
          rw [div_eq_mul_inv, mul_inv, inv_exp_neg, show ((1 / 2 : ℝ))⁻¹ = 2 by norm_num]
          ring
  have hr0 : ‖r0 τ‖ ≤ C4 ^ 2 * C6 * scale τ := by
    have hE14 : r0 τ = (τ : ℂ) * (E4Fun τ ^ 2 * E6Fun τ) := rfl
    rw [hE14, norm_mul, norm_mul, norm_pow]
    have h1' : ‖E4Fun τ‖ ^ 2 ≤ C4 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hE4 2
    have h2' : ‖E4Fun τ‖ ^ 2 * ‖E6Fun τ‖ ≤ C4 ^ 2 * C6 :=
      mul_le_mul h1' hE6 (norm_nonneg _) (by positivity)
    calc ‖(τ : ℂ)‖ * (‖E4Fun τ‖ ^ 2 * ‖E6Fun τ‖) ≤ scale τ * (C4 ^ 2 * C6) :=
          mul_le_mul hts h2' (by positivity) hs0.le
      _ = C4 ^ 2 * C6 * scale τ := by ring
  have hr2 : ‖r2 τ‖ ≤ C2t * (C4 * C6) * scale τ := by
    have hE10 : r2 τ = Compact.phi2t τ * (E4Fun τ * E6Fun τ) := rfl
    rw [hE10, norm_mul, norm_mul]
    have h2' : ‖E4Fun τ‖ * ‖E6Fun τ‖ ≤ C4 * C6 := mul_le_mul hE4 hE6 (norm_nonneg _) hC4.le
    calc ‖Compact.phi2t τ‖ * (‖E4Fun τ‖ * ‖E6Fun τ‖) ≤ (C2t * scale τ) * (C4 * C6) :=
          mul_le_mul hphi2 h2' (by positivity) (by positivity)
      _ = C2t * (C4 * C6) * scale τ := by ring
  have hR0 : ‖R0 τ‖ ≤ C1 * C4 ^ 3 * scale τ := by
    have hE : R0 τ = Compact.phi1 τ * E4Fun τ ^ 3 := rfl
    rw [hE, norm_mul, norm_pow]
    have h2' : ‖E4Fun τ‖ ^ 3 ≤ C4 ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hE4 3
    calc ‖Compact.phi1 τ‖ * ‖E4Fun τ‖ ^ 3 ≤ (C1 * scale τ) * C4 ^ 3 :=
          mul_le_mul hphi1 h2' (by positivity) (by positivity)
      _ = C1 * C4 ^ 3 * scale τ := by ring
  have hr1 : ‖r1 τ‖ ≤ 2 * C1 * scale τ := by
    have hE : r1 τ = Compact.phi1 τ * DeltaFun τ := rfl
    rw [hE, norm_mul]
    calc ‖Compact.phi1 τ‖ * ‖DeltaFun τ‖ ≤ (C1 * scale τ) * 2 := by
          refine mul_le_mul hphi1 ?_ (norm_nonneg _) (by positivity)
          have h2 : 2 * Real.exp (-(2 * Real.pi * τ.im)) ≤ 2 := by
            have := exp_neg_two_pi_im_le_one τ
            linarith
          exact le_trans hΔup h2
      _ = 2 * C1 * scale τ := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans hr0 ?_
    rw [hCdef, hExpand]
    have h2 : (0:ℝ) ≤ 2 * scale τ := by positivity
    have ha : (0:ℝ) ≤ C4 ^ 2 * C6 * scale τ := by positivity
    have hb : (0:ℝ) ≤ C2t * (C4 * C6) * scale τ := by positivity
    have hc : (0:ℝ) ≤ C1 * C4 ^ 3 * scale τ := by positivity
    have hd : (0:ℝ) ≤ 2 * C1 * scale τ := by positivity
    have he : (0:ℝ) ≤ 2 * C4 ^ 3 * scale τ := by positivity
    linarith
  · refine le_trans hr2 ?_
    rw [hCdef, hExpand]
    have h2 : (0:ℝ) ≤ 2 * scale τ := by positivity
    have ha : (0:ℝ) ≤ C4 ^ 2 * C6 * scale τ := by positivity
    have hb : (0:ℝ) ≤ C2t * (C4 * C6) * scale τ := by positivity
    have hc : (0:ℝ) ≤ C1 * C4 ^ 3 * scale τ := by positivity
    have hd : (0:ℝ) ≤ 2 * C1 * scale τ := by positivity
    have he : (0:ℝ) ≤ 2 * C4 ^ 3 * scale τ := by positivity
    linarith
  · refine le_trans hR0 ?_
    rw [hCdef, hExpand]
    have h2 : (0:ℝ) ≤ 2 * scale τ := by positivity
    have ha : (0:ℝ) ≤ C4 ^ 2 * C6 * scale τ := by positivity
    have hb : (0:ℝ) ≤ C2t * (C4 * C6) * scale τ := by positivity
    have hc : (0:ℝ) ≤ C1 * C4 ^ 3 * scale τ := by positivity
    have hd : (0:ℝ) ≤ 2 * C1 * scale τ := by positivity
    have he : (0:ℝ) ≤ 2 * C4 ^ 3 * scale τ := by positivity
    linarith
  · refine le_trans hr1 ?_
    rw [hCdef, hExpand]
    have h2 : (0:ℝ) ≤ 2 * scale τ := by positivity
    have ha : (0:ℝ) ≤ C4 ^ 2 * C6 * scale τ := by positivity
    have hb : (0:ℝ) ≤ C2t * (C4 * C6) * scale τ := by positivity
    have hc : (0:ℝ) ≤ C1 * C4 ^ 3 * scale τ := by positivity
    have hd : (0:ℝ) ≤ 2 * C1 * scale τ := by positivity
    have he : (0:ℝ) ≤ 2 * C4 ^ 3 * scale τ := by positivity
    linarith
  · refine le_trans hj ?_
    rw [hCdef, hExpand]
    have h2 : (0:ℝ) ≤ 2 * Real.exp (2 * Real.pi * τ.im) := by positivity
    have ha : (0:ℝ) ≤ C4 ^ 2 * C6 * Real.exp (2 * Real.pi * τ.im) := by positivity
    have hb : (0:ℝ) ≤ C2t * (C4 * C6) * Real.exp (2 * Real.pi * τ.im) := by positivity
    have hc : (0:ℝ) ≤ C1 * C4 ^ 3 * Real.exp (2 * Real.pi * τ.im) := by positivity
    have hd : (0:ℝ) ≤ 2 * C1 * Real.exp (2 * Real.pi * τ.im) := by positivity
    have he : (0:ℝ) ≤ 2 * C4 ^ 3 * Real.exp (2 * Real.pi * τ.im) := by positivity
    linarith
  · refine le_trans hΔup ?_
    rw [hCdef]
    have he : Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 := exp_neg_two_pi_im_le_one τ
    have ha : (0:ℝ) ≤ C4 ^ 2 * C6 := by positivity
    have hb : (0:ℝ) ≤ C2t * (C4 * C6) := by positivity
    have hc : (0:ℝ) ≤ C1 * C4 ^ 3 := by positivity
    have hd : (0:ℝ) ≤ 2 * C1 := by positivity
    have hf : (0:ℝ) ≤ 2 * C4 ^ 3 := by positivity
    linarith
  · refine le_trans hΔinv ?_
    rw [hCdef, hExpand]
    have h2 : (0:ℝ) ≤ 2 * Real.exp (2 * Real.pi * τ.im) := by positivity
    have ha : (0:ℝ) ≤ C4 ^ 2 * C6 * Real.exp (2 * Real.pi * τ.im) := by positivity
    have hb : (0:ℝ) ≤ C2t * (C4 * C6) * Real.exp (2 * Real.pi * τ.im) := by positivity
    have hc : (0:ℝ) ≤ C1 * C4 ^ 3 * Real.exp (2 * Real.pi * τ.im) := by positivity
    have hd : (0:ℝ) ≤ 2 * C1 * Real.exp (2 * Real.pi * τ.im) := by positivity
    have he : (0:ℝ) ≤ 2 * C4 ^ 3 * Real.exp (2 * Real.pi * τ.im) := by positivity
    linarith

/-- The same bounds with a single constant `D ≥ 24`. -/
theorem tau_atom_bounds_D : ∃ D : ℝ, 24 ≤ D ∧ ∀ τ : ℍ, Funnel τ →
    ‖r0 τ‖ ≤ D * scale τ ∧
    ‖r2 τ‖ ≤ D * scale τ ∧
    ‖R0 τ‖ ≤ D * scale τ ∧
    ‖r1 τ‖ ≤ D * scale τ ∧
    ‖jInvariantFun τ‖ ≤ D * Real.exp (2 * Real.pi * τ.im) ∧
    ‖DeltaFun τ‖ ≤ D ∧
    ‖(DeltaFun τ)⁻¹‖ ≤ D * Real.exp (2 * Real.pi * τ.im) := by
  obtain ⟨C, hC, hb⟩ := tau_atom_bounds
  refine ⟨C + 24, by linarith, fun τ hτ => ?_⟩
  obtain ⟨h0, h2, hR0, h1, hj, hΔ, hΔinv⟩ := hb τ hτ
  have hs1 : (1 : ℝ) ≤ scale τ := one_le_scale τ
  have hs0 : (0 : ℝ) ≤ scale τ := (scale_pos τ).le
  have hCn : C ≤ C + 24 := by linarith
  have hke : (0:ℝ) ≤ Real.exp (2 * Real.pi * τ.im) := (Real.exp_pos _).le
  have hke' : (0:ℝ) ≤ Real.exp (-(2 * Real.pi * τ.im)) := (Real.exp_pos _).le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans h0 (mul_le_mul_of_nonneg_right hCn hs0)
  · exact le_trans h2 (mul_le_mul_of_nonneg_right hCn hs0)
  · exact le_trans hR0 (mul_le_mul_of_nonneg_right hCn hs0)
  · exact le_trans h1 (mul_le_mul_of_nonneg_right hCn hs0)
  · exact le_trans hj (mul_le_mul_of_nonneg_right hCn hke)
  · simpa only [mul_one] using (le_trans hΔ (show C ≤ C + 24 by linarith) :
      ‖DeltaFun τ‖ ≤ C + 24)
  · exact le_trans hΔinv (mul_le_mul_of_nonneg_right hCn hke)

end K24F

end

end Work.Asymptotics
