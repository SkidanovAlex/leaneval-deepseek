import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.funnelTailQuant
import Submission.Work.Asymptotics.KPlus_eight_decomposition
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.KPlusFunnel.Atoms
import Submission.Work.Asymptotics.E4Fun_sub_one_explicit
import Submission.Work.Asymptotics.DeltaFun_funnel_lower_sharp
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.Asymptotics.funnelTailKPlus8
import Submission.Work.Asymptotics.KPlus8FunnelAux
import Submission.Work.Asymptotics.Compact.kplus8_tail_core
import Submission.Work.Asymptotics.funnel_divisor_lower
import Submission.Work.Asymptotics.Funnel24Aux

set_option maxHeartbeats 1000000

namespace Work.Asymptotics

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-! ## The three remainder terms of `Compact.KPlus8_sub_Gplus8_decomp`

The decomposition `Compact.KPlus8_sub_Gplus8_decomp` writes

  `K₊^{(8)}(τ,z) - 𝒢₊^{(8)}(τ,z) = (tailC)⁻¹ (Φ₁ + Φ₂ + Φ₃)`

with `Φ₁ = ΦMain`, `Φ₂ = ΦDiv`, `Φ₃ = ΦCorr`.  On the funnel each of the three is
`O((scale τ)^N (1+t)^M e^{-2π(t - Im τ)})`: the exponential growth `e^{2π Im τ}` of the
`τ`-atoms is absorbed by the `z`-atoms (the combination `Δ(z) j(τ)` carrying `e^{-2π t}`),
and the denominator `Δ(z)(j τ - j z)` is bounded below by `1/16` uniformly
(`Work.Asymptotics.funnel_divisor_lower`). -/

/-- **`Φ₁` is `O(scale τ · (1+t)² e^{-2π(t - Im τ)})` on the funnel.** -/
private theorem PhiMain_funnel_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.PhiMain τ z‖ ≤ C * scale τ * (1 + t) ^ 2
        * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
  obtain ⟨B, hB1, hzAtom⟩ := KPlus8_zAtom_bounds
  obtain ⟨C6, hC6, hE6⟩ := exists_E6_Funnel_bound
  obtain ⟨C0, hC0, hphi0⟩ := funnel_phi0_bound
  have hB0 : (0:ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
  refine ⟨B * (C6 * (1 + B + 12 / Real.pi) + 3 * C0 + 1) + 1, by positivity, ?_⟩
  intro τ z t hτ ht hz
  have ht3 : (3 : ℝ) ≤ t := by have := hτ.2; linarith
  have ht0 : (0 : ℝ) < t := by linarith
  have hscalepos : (0:ℝ) < scale τ := scale_pos τ
  obtain ⟨hE2s, hE4s, hE6s, hDz, hE2b, hE4b, hE6b, hph1, hph2⟩ := hzAtom z t ht3 hz
  have hzn : ‖(z : ℂ)‖ = t := ft_norm_coe hz (le_of_lt ht0)
  have hsq : ‖(z : ℂ) ^ 2‖ ≤ (1 + t) ^ 2 :=
    funnel_z_sq_norm_le z t (le_of_lt ht0) hz
  have hX1 : ‖(z : ℂ) ^ 2 * (1 + E2Fun z)‖ ≤ (1 + B) * (1 + t) ^ 2 := by
    rw [norm_mul]
    have h1b : ‖(1:ℂ) + E2Fun z‖ ≤ 1 + B := by
      have h := norm_add_le (1:ℂ) (E2Fun z)
      rw [norm_one] at h; linarith
    have h3 : (0:ℝ) ≤ (1 + t)^2 := by positivity
    calc ‖(z:ℂ)^2‖ * ‖(1:ℂ) + E2Fun z‖ ≤ (1+t)^2 * (1+B) := mul_le_mul hsq h1b (norm_nonneg _) h3
      _ = (1+B)*(1+t)^2 := by ring
  have hX2 : ‖(12:ℂ) * Complex.I * (z : ℂ) / (Real.pi : ℂ)‖ ≤ (12 / Real.pi) * (1 + t) ^ 2 := by
    have h1 : ‖(12:ℂ) * Complex.I * (z:ℂ) / (Real.pi:ℂ)‖ = 12 * t / Real.pi := by
      rw [norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, hzn,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [h1, show (12 * t / Real.pi) = (12 / Real.pi) * t by ring]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith
  have hX : ‖-((z:ℂ)^2 * (1 + E2Fun z)) + 12 * Complex.I * (z:ℂ) / (Real.pi:ℂ)‖
      ≤ (1 + B + 12 / Real.pi) * (1 + t) ^ 2 := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_neg]
    have := add_le_add hX1 hX2
    linarith
  have hBr : ‖(τ:ℂ) * E6Fun τ * (-((z:ℂ)^2 * (1 + E2Fun z)) + 12 * Complex.I * (z:ℂ) / (Real.pi:ℂ))
      + 2 * phi0 τ * E4Fun τ * (z:ℂ)^2‖
      ≤ (C6 * (1 + B + 12/Real.pi) + 3*C0) * scale τ * (1+t)^2 := by
    refine le_trans (norm_add_le _ _) ?_
    have hτ6 : ‖(τ:ℂ) * E6Fun τ‖ ≤ scale τ * C6 := by
      rw [norm_mul]
      exact mul_le_mul (coe_norm_le_scale τ) (hE6 τ hτ) (norm_nonneg _) (by positivity)
    have h1 : ‖(τ:ℂ) * E6Fun τ * (-((z:ℂ)^2 * (1 + E2Fun z)) + 12 * Complex.I * (z:ℂ) / (Real.pi:ℂ))‖
        ≤ (scale τ * C6) * ((1+B+12/Real.pi)*(1+t)^2) := by
      rw [norm_mul]
      exact mul_le_mul hτ6 hX (norm_nonneg _) (by positivity)
    have h2 : ‖(2:ℂ) * phi0 τ * E4Fun τ * (z:ℂ)^2‖ ≤ 3 * C0 * scale τ * (1+t)^2 := by
      rw [norm_mul, norm_mul, norm_mul, show ‖(2:ℂ)‖ = 2 by norm_num]
      have hE4 : ‖E4Fun τ‖ ≤ 3/2 := E4_funnel_upper' τ hτ
      calc 2 * ‖phi0 τ‖ * ‖E4Fun τ‖ * ‖(z:ℂ)^2‖
          ≤ 2 * (C0 * scale τ) * (3/2) * (1+t)^2 := by
            refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (hphi0 τ hτ) (by norm_num)) hE4 (norm_nonneg _) (by positivity)) hsq (norm_nonneg _) (by positivity)
        _ = 3 * C0 * scale τ * (1+t)^2 := by ring
    have hsum := add_le_add h1 h2
    have hcomb : (scale τ * C6) * ((1+B+12/Real.pi)*(1+t)^2) + 3*C0*scale τ*(1+t)^2
        = (C6 * (1 + B + 12/Real.pi) + 3*C0) * scale τ * (1+t)^2 := by ring
    linarith
  have he_le : Real.exp (-(2 * Real.pi * t)) ≤ Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, τ.im_pos]
  have hE2s' : ‖E2Fun z - 1‖ ≤ B * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    refine le_trans hE2s ?_
    exact mul_le_mul_of_nonneg_left he_le hB0.le
  have hfac : (0:ℝ) ≤ scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t-τ.im))) := by
    have := scale_pos τ; positivity
  calc ‖Compact.PhiMain τ z‖
      = ‖E2Fun z - 1‖ * ‖(τ:ℂ) * E6Fun τ * (-((z:ℂ)^2 * (1+E2Fun z)) + 12*Complex.I*(z:ℂ)/(Real.pi:ℂ)) + 2*phi0 τ*E4Fun τ*(z:ℂ)^2‖ := by
          rw [Compact.PhiMain, norm_mul]
    _ ≤ (B * Real.exp (-(2*Real.pi*(t-τ.im)))) * ((C6 * (1+B+12/Real.pi) + 3*C0) * scale τ * (1+t)^2) :=
        mul_le_mul hE2s' hBr (norm_nonneg _) (by positivity)
    _ = (B * (C6 * (1+B+12/Real.pi) + 3*C0)) * scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t-τ.im))) := by ring
    _ ≤ (B * (C6 * (1+B+12/Real.pi) + 3*C0 + 1) + 1) * scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t-τ.im))) := by
        have hble : B * (C6 * (1+B+12/Real.pi) + 3*C0) ≤ B * (C6 * (1+B+12/Real.pi) + 3*C0 + 1) + 1 := by
          nlinarith [hB0.le, hC6.le, hC0.le, Real.pi_pos]
        calc (B * (C6*(1+B+12/Real.pi)+3*C0)) * scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t-τ.im)))
            = (B * (C6*(1+B+12/Real.pi)+3*C0)) * (scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t-τ.im)))) := by ring
          _ ≤ (B * (C6*(1+B+12/Real.pi)+3*C0+1)+1) * (scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t-τ.im)))) := mul_le_mul_of_nonneg_right hble hfac
          _ = (B * (C6*(1+B+12/Real.pi)+3*C0+1)+1) * scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t-τ.im))) := by ring

/-- **`Φ₂` is `O(scale τ · (1+t)² e^{-2π(t - Im τ)})` on the funnel.** -/
private theorem PhiDiv_funnel_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.PhiDiv τ z‖ ≤ C * scale τ * (1 + t) ^ 2
        * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
  obtain ⟨C2, hC2, hphi2⟩ := funnel_phi2_bound
  obtain ⟨C6, hC6, hE6⟩ := exists_E6_Funnel_bound
  set K : ℝ := (C2 * C6 * 2) * (27 / 2) * 16 with hKdef
  refine ⟨K + 1, by positivity, ?_⟩
  intro τ z t hτ ht hz
  have ht0 : (0 : ℝ) < t := by have := hτ.2; linarith
  have hscalepos : (0:ℝ) < scale τ := scale_pos τ
  have hDJ : (1 / 16 : ℝ) ≤ ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ :=
    funnel_divisor_lower τ z t hτ ht hz
  have hDJinv : ‖(DeltaFun z * (jInvariantFun τ - jInvariantFun z))⁻¹‖ ≤ 16 := by
    rw [norm_inv]
    exact le_trans (inv_anti₀ (by norm_num : (0:ℝ) < 1/16) hDJ) (le_of_eq (by norm_num))
  have hid : Compact.PhiDiv τ z
      = phi2 τ * E6Fun τ * (E4Fun τ)⁻¹ * (z:ℂ)^2
        * (DeltaFun z * jInvariantFun τ)
        * (DeltaFun z * (jInvariantFun τ - jInvariantFun z))⁻¹ := by
    have hΔτ : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
    have hΔz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
    have hJ : jInvariantFun τ - jInvariantFun z ≠ 0 := by
      intro h0
      rw [h0, mul_zero, norm_zero] at hDJ
      norm_num at hDJ
    have hE4ne : E4Fun τ ≠ 0 := funnel_E4_ne_zero τ hτ
    rw [Compact.PhiDiv]
    rw [show jInvariantFun τ = E4Fun τ ^ 3 / DeltaFun τ from rfl,
        show jInvariantFun z = E4Fun z ^ 3 / DeltaFun z from rfl,
        show E14Fun τ = E4Fun τ ^ 2 * E6Fun τ from rfl]
    field_simp
  have hzsq : ‖(z:ℂ)^2‖ ≤ (1+t)^2 := funnel_z_sq_norm_le z t (le_of_lt ht0) hz
  have he2 : ‖DeltaFun z * jInvariantFun τ‖ ≤ (27/2) * Real.exp (-(2*Real.pi*(t - τ.im))) :=
    funnel_Delta_jTau_exp τ z t hτ ht hz
  have h1 : ‖phi2 τ‖ ≤ C2 * scale τ := hphi2 τ hτ
  have h2 : ‖E6Fun τ‖ ≤ C6 := hE6 τ hτ
  have h3 : ‖(E4Fun τ)⁻¹‖ ≤ 2 := funnel_E4_inv_le τ hτ
  have hmain : ‖Compact.PhiDiv τ z‖
      ≤ K * (scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im)))) := by
    rw [hid, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
    calc ‖phi2 τ‖ * ‖E6Fun τ‖ * ‖(E4Fun τ)⁻¹‖ * ‖(z:ℂ)^2‖ * ‖DeltaFun z * jInvariantFun τ‖
          * ‖(DeltaFun z * (jInvariantFun τ - jInvariantFun z))⁻¹‖
        ≤ (C2 * scale τ) * C6 * 2 * (1+t)^2 * ((27/2) * Real.exp (-(2*Real.pi*(t - τ.im)))) * 16 := by
          refine mul_le_mul
            (mul_le_mul
              (mul_le_mul
                (mul_le_mul
                  (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
                  h3 (norm_nonneg _) (by positivity))
                hzsq (norm_nonneg _) (by positivity))
              he2 (norm_nonneg _) (by positivity))
            hDJinv (norm_nonneg _) (by positivity)
      _ = K * (scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im)))) := by rw [hKdef]; ring
  have hfac : (0:ℝ) ≤ scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im))) := by positivity
  have hfinal : ‖Compact.PhiDiv τ z‖ ≤ (K + 1) * scale τ * (1 + t) ^ 2
        * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    calc ‖Compact.PhiDiv τ z‖
        ≤ K * (scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im)))) := hmain
      _ ≤ (K + 1) * (scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im)))) :=
          mul_le_mul_of_nonneg_right (by linarith) hfac
      _ = (K + 1) * scale τ * (1 + t) ^ 2 * Real.exp (-(2 * Real.pi * (t - τ.im))) := by ring
  exact hfinal

/-- **`Φ₃` is `O((scale τ)³ · (1+t)² e^{-2π(t - Im τ)})` on the funnel.** -/
private theorem PhiCorr_funnel_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (τ z : ℍ) (t : ℝ), Funnel τ → τ.im + 1 ≤ t →
      (z : ℂ) = (t : ℂ) * Complex.I →
      ‖Compact.PhiCorr τ z‖ ≤ C * (scale τ)^3 * (1 + t) ^ 2
        * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
  obtain ⟨B, hB1, hzAtom⟩ := KPlus8_zAtom_bounds
  obtain ⟨C6, hC6, hE6⟩ := exists_E6_Funnel_bound
  obtain ⟨C0, hC0, hphi0⟩ := funnel_phi0_bound
  have hB0 : (0:ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
  set K2 : ℝ := B ^ 2 * (B + 2) + 27 / 2 with hK2def
  set K : ℝ := (C6 * B * K2 + 3 * C0 * B * K2) * 16 with hKdef
  refine ⟨K + 1, by positivity, ?_⟩
  intro τ z t hτ ht hz
  have ht3 : (3 : ℝ) ≤ t := by have := hτ.2; linarith
  have hscalepos : (0:ℝ) < scale τ := scale_pos τ
  have hscale1 : (1:ℝ) ≤ scale τ := one_le_scale τ
  obtain ⟨hE2s, hE4s, hE6s, hDz, hE2b, hE4b, hE6b, hph1, hph2⟩ := hzAtom z t ht3 hz
  have hDJ : (1 / 16 : ℝ) ≤ ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ :=
    funnel_divisor_lower τ z t hτ ht hz
  have hDJinv : ‖(DeltaFun z * (jInvariantFun τ - jInvariantFun z))⁻¹‖ ≤ 16 := by
    rw [norm_inv]
    exact le_trans (inv_anti₀ (by norm_num : (0:ℝ) < 1/16) hDJ) (le_of_eq (by norm_num))
  have hele : Real.exp (-(2 * Real.pi * t)) ≤ Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, τ.im_pos]
  have hepos : (0:ℝ) < Real.exp (-(2 * Real.pi * (t - τ.im))) := Real.exp_pos _
  have hbr8 : ‖E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ‖
      ≤ K2 * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    have heq : E8Fun z - E4Fun z ^ 3 = E4Fun z ^ 2 * (1 - E4Fun z) := by
      rw [show E8Fun z = E4Fun z ^ 2 from rfl]; ring
    have h1 : ‖E4Fun z ^ 2 * (1 - E4Fun z)‖ ≤ B ^ 3 * Real.exp (-(2 * Real.pi * t)) := by
      rw [norm_mul, norm_sub_rev]
      calc ‖E4Fun z ^ 2‖ * ‖E4Fun z - 1‖ ≤ B ^ 2 * (B * Real.exp (-(2 * Real.pi * t))) := by
            refine mul_le_mul ?_ hE4s (norm_nonneg _) (by positivity)
            rw [norm_pow]
            exact pow_le_pow_left₀ (norm_nonneg _) hE4b 2
        _ = B ^ 3 * Real.exp (-(2 * Real.pi * t)) := by ring
    have h2 : ‖DeltaFun z * jInvariantFun τ‖ ≤ (27/2) * Real.exp (-(2*Real.pi*(t - τ.im))) :=
      funnel_Delta_jTau_exp τ z t hτ ht hz
    have h3 : B ^ 3 * Real.exp (-(2 * Real.pi * t)) ≤ B ^ 3 * Real.exp (-(2 * Real.pi * (t - τ.im))) :=
      mul_le_mul_of_nonneg_left hele (by positivity)
    have h4 : E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ
        = E4Fun z ^ 2 * (1 - E4Fun z) + DeltaFun z * jInvariantFun τ := by rw [heq]
    rw [h4]
    refine le_trans (norm_add_le _ _) ?_
    have h5 : B ^ 3 + 27/2 ≤ K2 := by rw [hK2def]; nlinarith [hB1]
    calc ‖E4Fun z ^ 2 * (1 - E4Fun z)‖ + ‖DeltaFun z * jInvariantFun τ‖
        ≤ B ^ 3 * Real.exp (-(2 * Real.pi * (t - τ.im))) + (27/2) * Real.exp (-(2*Real.pi*(t - τ.im))) :=
          add_le_add (le_trans h1 h3) h2
      _ = (B ^ 3 + 27/2) * Real.exp (-(2 * Real.pi * (t - τ.im))) := by ring
      _ ≤ K2 * Real.exp (-(2 * Real.pi * (t - τ.im))) := mul_le_mul_of_nonneg_right h5 hepos.le
  have hbr10 : ‖E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ‖
      ≤ K2 * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    have heq : E10Fun z - E4Fun z ^ 3 = E4Fun z * (E6Fun z - E4Fun z ^ 2) := by
      rw [show E10Fun z = E4Fun z * E6Fun z from rfl]; ring
    have h1 : ‖E4Fun z * (E6Fun z - E4Fun z ^ 2)‖ ≤ B ^ 2 * (B + 2) * Real.exp (-(2 * Real.pi * t)) := by
      have h6 : ‖E6Fun z - E4Fun z ^ 2‖ ≤ (B + B * (B + 1)) * Real.exp (-(2 * Real.pi * t)) := by
        have hs : E4Fun z ^ 2 - 1 = (E4Fun z - 1) * (E4Fun z + 1) := by ring
        have hsp : E6Fun z - E4Fun z ^ 2 = (E6Fun z - 1) - (E4Fun z ^ 2 - 1) := by ring
        have h7 : ‖E4Fun z + 1‖ ≤ B + 1 := by
          have h := norm_add_le (E4Fun z) (1:ℂ); rw [norm_one] at h; linarith
        have h8 : ‖(E4Fun z - 1) * (E4Fun z + 1)‖ ≤ (B * Real.exp (-(2*Real.pi*t))) * (B + 1) := by
          rw [norm_mul]
          exact mul_le_mul hE4s h7 (norm_nonneg _) (by positivity)
        rw [hsp]
        calc ‖(E6Fun z - 1) - (E4Fun z ^ 2 - 1)‖
            ≤ ‖E6Fun z - 1‖ + ‖E4Fun z ^ 2 - 1‖ := norm_sub_le _ _
          _ = ‖E6Fun z - 1‖ + ‖(E4Fun z - 1) * (E4Fun z + 1)‖ := by rw [hs]
          _ ≤ B * Real.exp (-(2*Real.pi*t)) + (B * Real.exp (-(2*Real.pi*t))) * (B + 1) :=
              add_le_add hE6s h8
          _ = (B + B * (B + 1)) * Real.exp (-(2 * Real.pi * t)) := by ring
      rw [norm_mul]
      calc ‖E4Fun z‖ * ‖E6Fun z - E4Fun z ^ 2‖
          ≤ B * ((B + B * (B + 1)) * Real.exp (-(2 * Real.pi * t))) :=
            mul_le_mul hE4b h6 (norm_nonneg _) (by positivity)
        _ = B ^ 2 * (B + 2) * Real.exp (-(2 * Real.pi * t)) := by ring
    have h2 : ‖DeltaFun z * jInvariantFun τ‖ ≤ (27/2) * Real.exp (-(2*Real.pi*(t - τ.im))) :=
      funnel_Delta_jTau_exp τ z t hτ ht hz
    have h3 : B ^ 2 * (B + 2) * Real.exp (-(2 * Real.pi * t)) ≤ B ^ 2 * (B + 2) * Real.exp (-(2 * Real.pi * (t - τ.im))) :=
      mul_le_mul_of_nonneg_left hele (by positivity)
    have h4 : E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ
        = E4Fun z * (E6Fun z - E4Fun z ^ 2) + DeltaFun z * jInvariantFun τ := by rw [heq]
    rw [h4]
    refine le_trans (norm_add_le _ _) ?_
    have h5 : B ^ 2 * (B + 2) + 27/2 = K2 := by rw [hK2def]
    calc ‖E4Fun z * (E6Fun z - E4Fun z ^ 2)‖ + ‖DeltaFun z * jInvariantFun τ‖
        ≤ B ^ 2 * (B + 2) * Real.exp (-(2 * Real.pi * (t - τ.im))) + (27/2) * Real.exp (-(2*Real.pi*(t - τ.im))) :=
          add_le_add (le_trans h1 h3) h2
      _ = K2 * Real.exp (-(2 * Real.pi * (t - τ.im))) := by rw [← h5]; ring
  have hτ6 : ‖(τ:ℂ) * E6Fun τ‖ ≤ scale τ * C6 := by
    rw [norm_mul]
    exact mul_le_mul (coe_norm_le_scale τ) (hE6 τ hτ) (norm_nonneg _) (by positivity)
  have hnum1 : ‖(τ:ℂ) * E6Fun τ * phitVec z 2 * (E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)‖
      ≤ (C6 * B * K2) * (scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im)))) := by
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖(τ:ℂ)‖ * ‖E6Fun τ‖ * ‖phitVec z 2‖ * ‖E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ‖
        ≤ (scale τ * C6) * (B * (1+t)^2) * (K2 * Real.exp (-(2 * Real.pi * (t - τ.im)))) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul (coe_norm_le_scale τ) (hE6 τ hτ) (norm_nonneg _) (by positivity)) hph2 (norm_nonneg _) (by positivity)) hbr8 (norm_nonneg _) (by positivity)
      _ = (C6 * B * K2) * (scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im)))) := by ring
  have hnum2 : ‖(2:ℂ) * phi0 τ * E4Fun τ * phitVec z 1 * (E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)‖
      ≤ (3 * C0 * B * K2) * (scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im)))) := by
    rw [norm_mul, norm_mul, norm_mul, norm_mul, show ‖(2:ℂ)‖ = 2 by norm_num]
    have hE4 : ‖E4Fun τ‖ ≤ 3/2 := E4_funnel_upper' τ hτ
    calc 2 * ‖phi0 τ‖ * ‖E4Fun τ‖ * ‖phitVec z 1‖ * ‖E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ‖
        ≤ 2 * (C0 * scale τ) * (3/2) * (B * (1+t)^2) * (K2 * Real.exp (-(2 * Real.pi * (t - τ.im)))) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (hphi0 τ hτ) (by norm_num)) hE4 (norm_nonneg _) (by positivity)) hph1 (norm_nonneg _) (by positivity)) hbr10 (norm_nonneg _) (by positivity)
      _ = (3 * C0 * B * K2) * (scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im)))) := by ring
  have hnum : ‖(τ:ℂ) * E6Fun τ * phitVec z 2 * (E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)
        - 2 * phi0 τ * E4Fun τ * phitVec z 1 * (E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)‖
      ≤ (C6 * B * K2 + 3 * C0 * B * K2) * (scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im)))) := by
    refine le_trans (norm_sub_le _ _) ?_
    have hsum := add_le_add hnum1 hnum2
    have hcomb : (C6 * B * K2) * (scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im))))
        + (3 * C0 * B * K2) * (scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im))))
        = (C6 * B * K2 + 3 * C0 * B * K2) * (scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im)))) := by ring
    linarith
  have hid : Compact.PhiCorr τ z
      = ((τ:ℂ) * E6Fun τ * phitVec z 2 * (E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)
        - 2 * phi0 τ * E4Fun τ * phitVec z 1 * (E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ))
        * (DeltaFun z * (jInvariantFun τ - jInvariantFun z))⁻¹ := by
    rw [Compact.PhiCorr, div_eq_mul_inv]
  have hs3 : scale τ ≤ scale τ ^ 3 := by
    have h2 : (1:ℝ) ≤ scale τ ^ 2 := by nlinarith [hscale1]
    calc scale τ = scale τ * 1 := by ring
      _ ≤ scale τ * scale τ ^ 2 := mul_le_mul_of_nonneg_left h2 hscalepos.le
      _ = scale τ ^ 3 := by ring
  have hfac : (0:ℝ) ≤ scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im))) := by positivity
  have hKnonneg : (0:ℝ) ≤ K := by rw [hKdef]; positivity
  calc ‖Compact.PhiCorr τ z‖
      = ‖(τ:ℂ) * E6Fun τ * phitVec z 2 * (E8Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)
        - 2 * phi0 τ * E4Fun τ * phitVec z 1 * (E10Fun z - E4Fun z ^ 3 + DeltaFun z * jInvariantFun τ)‖
        * ‖(DeltaFun z * (jInvariantFun τ - jInvariantFun z))⁻¹‖ := by rw [hid, norm_mul]
    _ ≤ ((C6 * B * K2 + 3 * C0 * B * K2) * (scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im))))) * 16 :=
        mul_le_mul hnum hDJinv (norm_nonneg _) (by positivity)
    _ = K * (scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im)))) := by rw [hKdef]; ring
    _ ≤ (K + 1) * (scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im)))) :=
        mul_le_mul_of_nonneg_right (by linarith) hfac
    _ ≤ (K + 1) * (scale τ ^ 3 * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im)))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs3 (by positivity)) (by positivity)
    _ = (K + 1) * scale τ ^ 3 * (1 + t) ^ 2 * Real.exp (-(2 * Real.pi * (t - τ.im))) := by ring

/-! ## The main theorem -/

/- **Funnel tail expansion of `K₊^{(8)}`.**

Same shape as the already-proved `Work.Asymptotics.KMinus_funnel_tail_eight`
(`Submission/Work/Asymptotics/KMinus_funnel_tail_eight.lean`) and
`Work.Asymptotics.KPlus_funnel_tail_twentyfour`
(`Submission/Work/Asymptotics/KPlus_funnel_tail_twentyfour.lean`), but for `K₊^{(8)}` against
the model `Work.Asymptotics.Compact.Gplus 8`.

Recipe (verified numerically; every input is already proved in this workspace):
* `Work.Asymptotics.KPlus_eight_decomposition` expands `KPlus 8 τ z` with `J = jτ - jz`;
  `Work.Asymptotics.funnelTailQuant.Gplus8_eq` rewrites `Compact.Gplus 8` in cancelled form.
* `Work.Asymptotics.Gplus8_eq`'s companion `Work.Kernels.TildeFacts.E2S_eq`
  (`E₂ˢ(z) = E₂(z) - 6i/(πz)`), `phitVec_zero`, and the `O(q)` expansions `E2Fun_two_term`,
  `E4Fun_two_term`, `E6Fun_two_term` control the `z`-atoms on `z = i t`, `t ≥ 3`.
* The uniform divisor bound `‖Δ(z)(j τ − j z)‖ ≥ 1/16` on the funnel
  (`τ ∈ DomainD`, `2 ≤ Im τ`, `t ≥ Im τ + 1`, `(z:ℂ) = t*I`) follows from
  `Work.Asymptotics.DeltaFun_funnel_lower_sharp` (`‖Δ τ‖ ≥ (1/2)e^{-2π Im τ}`),
  `Work.Asymptotics.E4Fun_sub_one_explicit` (`‖E₄ w − 1‖ ≤ 20000‖q(w)‖` for `Im w ≥ 1`),
  `Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun` (`Δ·j = E₄³`) and the sharp
  `DeltaFun_imagAxis_atTop`; the numerical comparisons `6.75 e^{-2π} ≤ 1/16`,
  `20000 e^{-2πt} ≤ 1/2` (`t ≥ 3`) are in `Submission/Work/Asymptotics/funnelTailKPlus8.lean`.
* `τ`-atom growth is in `Work.Asymptotics.funnelTailBasic` and
  `Submission/Work/Asymptotics/KPlusFunnel/Atoms.lean` (`phi8_eq`, `phi8_bound`, `jFunnel_bound`,
  `tau_cusp_forms`, `deltaFunnel_upper`).
* Expected residual rate is `e^{-2π(t-Im τ)}`; the conclusion only asks for
  `e^{-π(t-Im τ)}` with any polynomial `(scale τ)^N (1+t)^M`. -/
theorem KPlus_funnel_tail_eight :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Work.Kernels.KPlus 8 τ z - Work.Asymptotics.Compact.Gplus 8 τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * (t - τ.im))) := by
  obtain ⟨C1, hC1, hMain⟩ := PhiMain_funnel_bound
  obtain ⟨C2, hC2, hDiv⟩ := PhiDiv_funnel_bound
  obtain ⟨C3, hC3, hCorr⟩ := PhiCorr_funnel_bound
  set K : ℝ := ‖Compact.tailC⁻¹‖ * (C1 + C2 + C3) with hKdef
  refine ⟨K + 1, 3, 2, by positivity, by norm_num, by norm_num, ?_⟩
  intro τ z t hτ ht hz
  have ht3 : (3:ℝ) ≤ t := by have := hτ.2; linarith
  have hscalepos : (0:ℝ) < scale τ := scale_pos τ
  have hscale1 : (1:ℝ) ≤ scale τ := one_le_scale τ
  have hDJ : (1 / 16 : ℝ) ≤ ‖DeltaFun z * (jInvariantFun τ - jInvariantFun z)‖ :=
    funnel_divisor_lower τ z t hτ ht hz
  have hJsub : jInvariantFun τ - jInvariantFun z ≠ 0 := by
    intro h0
    rw [h0, mul_zero, norm_zero] at hDJ
    norm_num at hDJ
  have hJne : jInvariantFun τ ≠ jInvariantFun z := sub_ne_zero.mp hJsub
  have hdecomp := Compact.KPlus8_sub_Gplus8_decomp τ z hJne
  have hM := hMain τ z t hτ ht hz
  have hD := hDiv τ z t hτ ht hz
  have hC := hCorr τ z t hτ ht hz
  have hs3 : scale τ ≤ scale τ ^ 3 := by
    have h2 : (1:ℝ) ≤ scale τ ^ 2 := by nlinarith [hscale1]
    calc scale τ = scale τ * 1 := by ring
      _ ≤ scale τ * scale τ ^ 2 := mul_le_mul_of_nonneg_left h2 hscalepos.le
      _ = scale τ ^ 3 := by ring
  have hfac : (0:ℝ) ≤ (1+t)^2 * Real.exp (-(2 * Real.pi * (t - τ.im))) := by positivity
  have hsum : ‖Compact.PhiMain τ z + Compact.PhiDiv τ z + Compact.PhiCorr τ z‖
      ≤ (C1 + C2 + C3) * (scale τ)^3 * (1+t)^2 * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    have h1 := norm_add_le (Compact.PhiMain τ z + Compact.PhiDiv τ z) (Compact.PhiCorr τ z)
    have h2 := norm_add_le (Compact.PhiMain τ z) (Compact.PhiDiv τ z)
    have hM' : ‖Compact.PhiMain τ z‖ ≤ C1 * (scale τ)^3 * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im))) := by
      refine le_trans hM ?_
      calc C1 * scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im)))
          = C1 * (scale τ * ((1+t)^2 * Real.exp (-(2 * Real.pi * (t - τ.im))))) := by ring
        _ ≤ C1 * (scale τ^3 * ((1+t)^2 * Real.exp (-(2 * Real.pi * (t - τ.im))))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs3 hfac) hC1.le
        _ = C1 * (scale τ)^3 * (1+t)^2 * Real.exp (-(2 * Real.pi * (t - τ.im))) := by ring
    have hD' : ‖Compact.PhiDiv τ z‖ ≤ C2 * (scale τ)^3 * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im))) := by
      refine le_trans hD ?_
      calc C2 * scale τ * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im)))
          = C2 * (scale τ * ((1+t)^2 * Real.exp (-(2 * Real.pi * (t - τ.im))))) := by ring
        _ ≤ C2 * (scale τ^3 * ((1+t)^2 * Real.exp (-(2 * Real.pi * (t - τ.im))))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs3 hfac) hC2.le
        _ = C2 * (scale τ)^3 * (1+t)^2 * Real.exp (-(2 * Real.pi * (t - τ.im))) := by ring
    have hC' : ‖Compact.PhiCorr τ z‖ ≤ C3 * (scale τ)^3 * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im))) := hC
    have hcomb : C1 * (scale τ)^3 * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im)))
        + C2 * (scale τ)^3 * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im)))
        + C3 * (scale τ)^3 * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im)))
        = (C1 + C2 + C3) * (scale τ)^3 * (1+t)^2 * Real.exp (-(2*Real.pi*(t - τ.im))) := by ring
    linarith
  have hGplus : Compact.Gplus 8 τ z = Compact.Gplus8 τ z := by
    rw [Compact.Gplus]; simp
  rw [hGplus]
  have hmain : ‖Work.Kernels.KPlus 8 τ z - Compact.Gplus8 τ z‖
      ≤ K * (scale τ)^3 * (1+t)^2 * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
    have h1 : (0:ℝ) ≤ ‖Compact.tailC⁻¹‖ := norm_nonneg _
    calc ‖Work.Kernels.KPlus 8 τ z - Compact.Gplus8 τ z‖
        = ‖Compact.tailC⁻¹ * (Compact.PhiMain τ z + Compact.PhiDiv τ z + Compact.PhiCorr τ z)‖ := by rw [hdecomp]
      _ = ‖Compact.tailC⁻¹‖ * ‖Compact.PhiMain τ z + Compact.PhiDiv τ z + Compact.PhiCorr τ z‖ := by rw [norm_mul]
      _ ≤ ‖Compact.tailC⁻¹‖ * ((C1 + C2 + C3) * (scale τ)^3 * (1+t)^2 * Real.exp (-(2 * Real.pi * (t - τ.im)))) := mul_le_mul_of_nonneg_left hsum h1
      _ = K * (scale τ)^3 * (1+t)^2 * Real.exp (-(2 * Real.pi * (t - τ.im))) := by rw [hKdef]; ring
  have he2e1 : Real.exp (-(2 * Real.pi * (t - τ.im))) ≤ Real.exp (-(Real.pi * (t - τ.im))) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, ht]
  have hfac2 : (0:ℝ) ≤ K * (scale τ)^3 * (1+t)^2 := by positivity
  refine le_trans hmain ?_
  refine le_trans (mul_le_mul_of_nonneg_left he2e1 hfac2) ?_
  rw [Real.rpow_ofNat, Real.rpow_ofNat]
  have hK1 : K * (scale τ)^3 * (1+t)^2 * Real.exp (-(Real.pi*(t-τ.im)))
      ≤ (K + 1) * (scale τ)^3 * (1+t)^2 * Real.exp (-(Real.pi*(t-τ.im))) := by
    have hh : (0:ℝ) ≤ Real.exp (-(Real.pi*(t-τ.im))) := Real.exp_nonneg _
    have h2 : (0:ℝ) ≤ (scale τ)^3 * (1+t)^2 := by positivity
    have h3 : K * (scale τ)^3 * (1+t)^2 ≤ (K + 1) * (scale τ)^3 * (1+t)^2 := by
      calc K * (scale τ)^3 * (1+t)^2 = K * ((scale τ)^3 * (1+t)^2) := by ring
        _ ≤ (K+1) * ((scale τ)^3 * (1+t)^2) := mul_le_mul_of_nonneg_right (by linarith) h2
        _ = (K+1) * (scale τ)^3 * (1+t)^2 := by ring
    calc K * (scale τ)^3 * (1+t)^2 * Real.exp (-(Real.pi*(t-τ.im)))
        = (K * (scale τ)^3 * (1+t)^2) * Real.exp (-(Real.pi*(t-τ.im))) := rfl
      _ ≤ ((K+1) * (scale τ)^3 * (1+t)^2) * Real.exp (-(Real.pi*(t-τ.im))) :=
          mul_le_mul_of_nonneg_right h3 hh
      _ = (K+1) * (scale τ)^3 * (1+t)^2 * Real.exp (-(Real.pi*(t-τ.im))) := rfl
  exact hK1

end

end Work.Asymptotics
