/-
# Shared funnel facts for the `d = 8` tail expansion

Auxiliary facts used by the funnel tail expansion of `K₊^{(8)}`
(`Submission/Work/Asymptotics/KPlus_funnel_tail_eight.lean`) and by the bounds on the three
remainder terms `Compact.PhiMain`, `Compact.PhiDiv`, `Compact.PhiCorr` of the decomposition
`Compact.KPlus8_sub_Gplus8_decomp`:

* `funnel_E4_sub_one_le`, `funnel_E4_lower`, `funnel_E4_ne_zero`, `funnel_E4_inv_le` :
  the weight-four Eisenstein series is within `1/2` of `1` on the funnel;
* `funnel_phi0_bound`, `funnel_phi2_bound` : the two `τ`-atoms `φ₀`, `φ₂`;
* `funnel_E14_bound` : `E₁₄` is bounded on the funnel;
* `funnel_Delta_jTau_exp` : `‖Δ(z) j(τ)‖ ≤ (27/2) e^{-2π(t - Im τ)}` on the contour;
* `funnel_zAtom_bounds` : the `z`-atom bounds on the contour `z = i t`, `t ≥ 3`;
* `funnel_z_sq_norm_le` : `‖z²‖ ≤ (1+t)²` on the contour.
-/
import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.Compact.kplus8_tail_core
import Submission.Work.Asymptotics.funnel_divisor_lower
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.E4Fun_sub_one_explicit
import Submission.Work.Asymptotics.K24FBase

set_option maxHeartbeats 1000000

namespace Work.Asymptotics

open UpperHalfPlane

noncomputable section

open Work.Kernels

/-! ## `E₄` on the funnel -/

/-- `‖E₄ τ - 1‖ ≤ 1/2` on the funnel. -/
theorem funnel_E4_sub_one_le (τ : ℍ) (hτ : Funnel τ) : ‖E4Fun τ - 1‖ ≤ 1 / 2 := by
  have h1 : (1 : ℝ) ≤ τ.im := Funnel.im_one hτ
  have h := E4Fun_sub_one_explicit h1
  rw [norm_qParamFun] at h
  have h4 : Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 / 40000 :=
    ft_exp_neg_two_pi_im_le τ (by
      have : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      nlinarith [hτ.2, Real.pi_pos])
  have h6 : (20000 : ℝ) * Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 20000)
    linarith
  linarith

/-- `‖E₄ τ‖ ≥ 1/2` on the funnel. -/
theorem funnel_E4_lower (τ : ℍ) (hτ : Funnel τ) : (1 / 2 : ℝ) ≤ ‖E4Fun τ‖ := by
  have h := funnel_E4_sub_one_le τ hτ
  have hb := abs_norm_sub_norm_le (E4Fun τ) (1 : ℂ)
  rw [norm_one] at hb
  have h2 : -(1 / 2 : ℝ) ≤ ‖E4Fun τ‖ - 1 := (abs_le.mp (le_trans hb h)).1
  linarith

/-- `E₄ τ ≠ 0` on the funnel. -/
theorem funnel_E4_ne_zero (τ : ℍ) (hτ : Funnel τ) : E4Fun τ ≠ 0 := by
  intro h0
  have h := funnel_E4_lower τ hτ
  rw [h0, norm_zero] at h
  norm_num at h

/-- `‖(E₄ τ)⁻¹‖ ≤ 2` on the funnel. -/
theorem funnel_E4_inv_le (τ : ℍ) (hτ : Funnel τ) : ‖(E4Fun τ)⁻¹‖ ≤ 2 := by
  have h := funnel_E4_lower τ hτ
  rw [norm_inv]
  calc (‖E4Fun τ‖)⁻¹ ≤ ((1 / 2 : ℝ))⁻¹ := inv_anti₀ (by norm_num) h
    _ = 2 := by norm_num

/-! ## The `τ`-atoms `φ₀`, `φ₂`, `E₁₄` -/

/-- `‖φ₀ τ‖ ≤ C scale τ` on the funnel. -/
theorem funnel_phi0_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ → ‖Work.Kernels.phi0 τ‖ ≤ C * scale τ := by
  obtain ⟨C, hC, h⟩ := K24F.phi1_bound
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h' := h τ hτ
  simpa only [Compact.phi1, Work.Kernels.phi0] using h'

/-- `‖φ₂ τ‖ ≤ C scale τ` on the funnel. -/
theorem funnel_phi2_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ → ‖Work.Kernels.phi2 τ‖ ≤ C * scale τ := by
  obtain ⟨C, hC, h⟩ := K24F.phi2t_bound
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h' := h τ hτ
  simpa only [Compact.phi2t, Work.Kernels.phi2] using h'

/-- `‖E₁₄ τ‖ ≤ C` on the funnel. -/
theorem funnel_E14_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Funnel τ → ‖E14Fun τ‖ ≤ C := by
  obtain ⟨C4, hC4, h4⟩ := exists_E4_Funnel_bound
  obtain ⟨C6, hC6, h6⟩ := exists_E6_Funnel_bound
  refine ⟨C4 ^ 2 * C6 + 1, by positivity, fun τ hτ => ?_⟩
  have heq : E14Fun τ = E4Fun τ ^ 2 * E6Fun τ := rfl
  rw [heq, norm_mul, norm_pow]
  have h1 : ‖E4Fun τ‖ ^ 2 * ‖E6Fun τ‖ ≤ C4 ^ 2 * C6 :=
    mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (h4 τ hτ) 2) (h6 τ hτ) (norm_nonneg _)
      (by positivity)
  linarith

/-! ## `Δ(z) j(τ)` on the contour -/

/-- `‖Δ(z) j(τ)‖ ≤ (27/2) e^{-2π(t - Im τ)}` for `τ` in the funnel, `z = i t`,
`t ≥ Im τ + 1`. -/
theorem funnel_Delta_jTau_exp (τ z : ℍ) (t : ℝ) (hτ : Funnel τ) (ht : τ.im + 1 ≤ t)
    (hz : (z : ℂ) = (t : ℂ) * Complex.I) :
    ‖DeltaFun z * jInvariantFun τ‖
      ≤ (27 / 2) * Real.exp (-(2 * Real.pi * (t - τ.im))) := by
  refine le_trans (funnel_rho_exp τ z t hτ ht hz) (le_of_eq ?_)
  rw [sq, ← Real.exp_add]
  congr 1
  ring_nf

/-! ## The `z`-atoms on the contour -/

/-- The `z`-atom bounds on the contour `z = i t`, `t ≥ 3`. -/
theorem KPlus8_zAtom_bounds :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (z : ℍ) (t : ℝ), 3 ≤ t → (z : ℂ) = (t : ℂ) * Complex.I →
      ‖E2Fun z - 1‖ ≤ B * Real.exp (-(2 * Real.pi * t)) ∧
      ‖E4Fun z - 1‖ ≤ B * Real.exp (-(2 * Real.pi * t)) ∧
      ‖E6Fun z - 1‖ ≤ B * Real.exp (-(2 * Real.pi * t)) ∧
      ‖DeltaFun z‖ ≤ B * Real.exp (-(2 * Real.pi * t)) ∧
      ‖E2Fun z‖ ≤ B ∧
      ‖E4Fun z‖ ≤ B ∧
      ‖E6Fun z‖ ≤ B ∧
      ‖phitVec z 1‖ ≤ B * (1 + t) ^ 2 ∧
      ‖phitVec z 2‖ ≤ B * (1 + t) ^ 2 := by
  obtain ⟨B, hB1, h⟩ := Compact.imagAxis_cusp_bounds
  refine ⟨B, hB1, fun z t ht hz => ?_⟩
  have ht0 : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hw : z = Work.Kernels.imagAxis t ht0 :=
    UpperHalfPlane.ext (by rw [hz]; rfl)
  rw [hw]
  exact h t ht0 ht1

/-- `‖z²‖ ≤ (1+t)²` on the contour `z = i t`, `t ≥ 0`. -/
theorem funnel_z_sq_norm_le (z : ℍ) (t : ℝ) (ht0 : 0 ≤ t)
    (hz : (z : ℂ) = (t : ℂ) * Complex.I) : ‖(z : ℂ) ^ 2‖ ≤ (1 + t) ^ 2 := by
  have hzn : ‖(z : ℂ)‖ = t := ft_norm_coe hz ht0
  rw [norm_pow, hzn]
  nlinarith

end

end Work.Asymptotics
