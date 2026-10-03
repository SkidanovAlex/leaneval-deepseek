/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.Analysis.CzShift.Defs

/-!
# Pointwise bounds for the shifted Calderón–Zygmund kernels

This file proves `Work.Analysis.CzShift.kernel_bounds`: the pointwise size bound, the `L¹`
bound and the two Hölder-regularity estimates for the shifted kernels
`x ↦ σ⁻¹ Ψ((x - t σ)/σ)` attached to a rescaled Schwartz seed `Ψ` (see
`Work.Analysis.CzShift.IsCZSeed`).

These are the four estimates collected as (B.1)--(B.4) in Appendix B of
Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals of Math. **195** (2022).

The proof of the `L¹` bound uses the classical identity
`∫ x, (1 + x ^ 2)⁻¹ = π` from `Mathlib.Analysis.SpecialFunctions.ImproperIntegrals`
together with translation invariance and the scaling behaviour of Lebesgue measure.
-/

namespace Work.Analysis.CzShift

open MeasureTheory

set_option autoImplicit false

section Elementary

/-- **Comparison of the Cauchy weights.**  If `v` is within `1/2` of `u`, then the weight
`(1 + u ^ 2)⁻¹` is at most four times the weight `(1 + v ^ 2)⁻¹`. -/
lemma one_add_sq_le_four_mul {u v : ℝ} (h : |v - u| ≤ 1 / 2) :
    1 + u ^ 2 ≤ 4 * (1 + v ^ 2) := by
  have hu : |u| ≤ |v| + 1 / 2 := by
    have h1 : |u| ≤ |u - v| + |v| := by
      calc |u| = |(u - v) + v| := by ring_nf
        _ ≤ |u - v| + |v| := abs_add_le _ _
    rw [abs_sub_comm v u] at h
    linarith
  by_cases hc : |u| ≤ 1
  · have hu2 : u ^ 2 ≤ 1 := by
      have h' := pow_le_pow_left₀ (abs_nonneg u) hc 2
      rwa [sq_abs, one_pow] at h'
    nlinarith [sq_nonneg v]
  · have h1 : 1 < |u| := lt_of_not_ge hc
    have hv : |u| / 2 ≤ |v| := by linarith
    have hv2 : u ^ 2 / 4 ≤ v ^ 2 := by
      have h' := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ |u| / 2) hv 2
      rw [div_pow, sq_abs, sq_abs] at h'
      norm_num at h'
      linarith
    nlinarith

/-- **Comparison of the Cauchy weights, multiplicative form.**  If `|v| ≤ 2 |u|` then
`1 + v ^ 2 ≤ 4 (1 + u ^ 2)`. -/
lemma one_add_sq_le_four_mul_of_two_mul {u v : ℝ} (h : |v| ≤ 2 * |u|) :
    1 + v ^ 2 ≤ 4 * (1 + u ^ 2) := by
  have h2 : v ^ 2 ≤ 4 * u ^ 2 := by
    have h' := pow_le_pow_left₀ (abs_nonneg v) h 2
    rw [mul_pow, sq_abs, sq_abs] at h'
    norm_num at h'
    linarith
  nlinarith

end Elementary

/-- **Derivative bound.**  For a seed `Ψ` with derivative `Ψ'` bounded by `B / (1 + x ^ 2)`,
the derivative at a point `c` close to `u` is bounded by `4 B / (1 + u ^ 2)`. -/
lemma abs_deriv_le_of_abs_sub_le {Ψ Ψ' : ℝ → ℝ} {B : ℝ} (hseed : IsCZSeed Ψ Ψ' B)
    {u c : ℝ} (hc : |c - u| ≤ 1 / 2) :
    |Ψ' c| ≤ 4 * B / (1 + u ^ 2) := by
  have hB : 0 ≤ B := le_trans zero_le_one hseed.one_le
  have hA : 1 + u ^ 2 ≤ 4 * (1 + c ^ 2) := one_add_sq_le_four_mul hc
  have h2 : (1 + c ^ 2)⁻¹ ≤ 4 * (1 + u ^ 2)⁻¹ := by
    have h' : (1 : ℝ) / (1 + c ^ 2) ≤ 4 / (1 + u ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    simpa [div_eq_mul_inv] using h'
  calc |Ψ' c| ≤ B / (1 + c ^ 2) := hseed.bound' c
    _ = B * (1 + c ^ 2)⁻¹ := by ring
    _ ≤ B * (4 * (1 + u ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h2 hB
    _ = 4 * B / (1 + u ^ 2) := by ring

/-- **Increment bound.**  The increment of the seed over an interval of length at most `1/2`
is bounded by the length times the Cauchy weight at the left endpoint. -/
lemma abs_seed_sub_le {Ψ Ψ' : ℝ → ℝ} {B : ℝ} (hseed : IsCZSeed Ψ Ψ' B) {u h : ℝ}
    (hh : |h| ≤ 1 / 2) :
    |Ψ u - Ψ (u - h)| ≤ |h| * (4 * B / (1 + u ^ 2)) := by
  have hdiff : Differentiable ℝ Ψ := fun u => (hseed.hasDerivAt u).differentiableAt
  have hcont : Continuous Ψ := hdiff.continuous
  rcases eq_or_ne h 0 with rfl | hne
  · simp
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope Ψ Ψ' (by linarith : u < u - h)
      hcont.continuousOn (fun x _ => hseed.hasDerivAt x)
    rw [show (u - h) - u = -h by ring] at hc'
    have hdiff : Ψ u - Ψ (u - h) = h * Ψ' c := by
      rw [hc']
      field_simp
      ring
    have hcu : |c - u| ≤ 1 / 2 := by
      have h1 : 0 < c - u := by linarith [hc.1]
      rw [abs_of_pos h1]
      have h2 : |h| = -h := abs_of_neg hlt
      linarith [hc.2, hh, h2]
    calc |Ψ u - Ψ (u - h)| = |h * Ψ' c| := by rw [hdiff]
      _ = |h| * |Ψ' c| := abs_mul _ _
      _ ≤ |h| * (4 * B / (1 + u ^ 2)) :=
          mul_le_mul_of_nonneg_left (abs_deriv_le_of_abs_sub_le hseed hcu) (abs_nonneg h)
  · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope Ψ Ψ' (sub_lt_self u hgt)
      hcont.continuousOn (fun x _ => hseed.hasDerivAt x)
    rw [show u - (u - h) = h by ring] at hc'
    have hdiff : Ψ u - Ψ (u - h) = h * Ψ' c := by
      rw [hc']
      field_simp
    have hcu : |c - u| ≤ 1 / 2 := by
      have h1 : c - u < 0 := by linarith [hc.2]
      rw [abs_of_neg h1]
      have h2 : |h| = h := abs_of_pos hgt
      linarith [hc.1, hh, h2]
    calc |Ψ u - Ψ (u - h)| = |h * Ψ' c| := by rw [hdiff]
      _ = |h| * |Ψ' c| := abs_mul _ _
      _ ≤ |h| * (4 * B / (1 + u ^ 2)) :=
          mul_le_mul_of_nonneg_left (abs_deriv_le_of_abs_sub_le hseed hcu) (abs_nonneg h)

/-- The norm of a real number seen as a complex number. -/
lemma norm_ofReal_complex (r : ℝ) : ‖((r : ℝ) : ℂ)‖ = |r| := by simp

/-- The norm of the shifted kernel at `x`: `σ⁻¹ |Ψ((x - t σ)/σ)|`. -/
lemma shiftKernel_norm {Ψ : ℝ → ℝ} {σ : ℝ} (hσ : 0 < σ) (t x : ℝ) :
    ‖shiftKernel Ψ σ t x‖ = σ⁻¹ * |Ψ ((x - t * σ) / σ)| := by
  rw [shiftKernel, norm_ofReal_complex, abs_mul, abs_of_pos (inv_pos.mpr hσ)]

/-- The norm of the difference of the shifted kernel at `x - y` and at `x`. -/
lemma norm_shiftKernel_sub {Ψ : ℝ → ℝ} {σ : ℝ} (hσ : 0 < σ) (t x y : ℝ) :
    ‖shiftKernel Ψ σ t (x - y) - shiftKernel Ψ σ t x‖
      = σ⁻¹ * |Ψ ((x - t * σ) / σ - y / σ) - Ψ ((x - t * σ) / σ)| := by
  have harg : (x - y - t * σ) / σ = (x - t * σ) / σ - y / σ := by
    ring
  simp only [shiftKernel]
  rw [harg, ← Complex.ofReal_sub, norm_ofReal_complex, ← mul_sub, abs_mul,
    abs_of_pos (inv_pos.mpr hσ)]

/-- **The `L¹` bound.**  For a positive scale `σ` and any shift `t`,
`∫ x, (1 + ((x - t σ)/σ) ^ 2)⁻¹ = σ π`. -/
lemma integral_inv_one_add_sq_shift (σ t : ℝ) (hσ : 0 < σ) :
    ∫ x : ℝ, (1 + ((x - t * σ) / σ) ^ 2)⁻¹ = σ * Real.pi := by
  have h1 : ∫ x : ℝ, (1 + ((x - t * σ) / σ) ^ 2)⁻¹ = ∫ x : ℝ, (1 + (x / σ) ^ 2)⁻¹ :=
    integral_sub_right_eq_self (fun x : ℝ => (1 + (x / σ) ^ 2)⁻¹) (t * σ)
  have h2 : ∫ x : ℝ, (1 + (x / σ) ^ 2)⁻¹ = σ * Real.pi := by
    rw [Measure.integral_comp_div (g := fun x : ℝ => (1 + x ^ 2)⁻¹) σ,
      integral_univ_inv_one_add_sq, abs_of_pos hσ, smul_eq_mul]
  exact h1.trans h2

theorem kernel_bounds {Ψ Ψ' : ℝ → ℝ} {B : ℝ} (h : IsCZSeed Ψ Ψ' B) :
    (∀ σ t : ℝ, 0 < σ → ∀ x : ℝ, ‖shiftKernel Ψ σ t x‖ ≤ B / σ) ∧
    (∀ σ t : ℝ, 0 < σ → ∫ x, ‖shiftKernel Ψ σ t x‖ ≤ Real.pi * B) ∧
    (∀ σ t y : ℝ, 0 < σ → |y| ≤ σ / 2 → ∀ x : ℝ,
      ‖shiftKernel Ψ σ t (x - y) - shiftKernel Ψ σ t x‖
        ≤ (|y| / σ) * (4 * B / σ) * (1 + ((x - t * σ) / σ) ^ 2)⁻¹) ∧
    (∀ σ t L : ℝ, 0 < σ → 0 < L → |t| * σ ≤ L → ∀ y x : ℝ, |y| ≤ L / 2 → 50 * L ≤ |x| →
      ‖shiftKernel Ψ σ t (x - y) - shiftKernel Ψ σ t x‖
        ≤ 16 * B * σ⁻¹ * (1 + (x / σ) ^ 2)⁻¹) := by
  have hB : 0 ≤ B := le_trans zero_le_one h.one_le
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ t hσ x
    rw [shiftKernel_norm hσ t x]
    have h1 : |Ψ ((x - t * σ) / σ)| ≤ B := by
      calc |Ψ ((x - t * σ) / σ)| ≤ B / (1 + ((x - t * σ) / σ) ^ 2) := h.bound _
        _ ≤ B / 1 :=
            div_le_div_of_nonneg_left hB zero_lt_one (by nlinarith [sq_nonneg ((x - t * σ) / σ)])
        _ = B := by ring
    calc σ⁻¹ * |Ψ ((x - t * σ) / σ)| ≤ σ⁻¹ * B :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = B / σ := by ring
  · intro σ t hσ
    have hσne : σ ≠ 0 := hσ.ne'
    have hI : Integrable (fun x : ℝ => (1 + ((x - t * σ) / σ) ^ 2)⁻¹) :=
      (integrable_inv_one_add_sq.comp_div (R := σ) hσne).comp_sub_right (t * σ)
    have hIg : Integrable (fun x : ℝ => σ⁻¹ * B * (1 + ((x - t * σ) / σ) ^ 2)⁻¹) :=
      hI.const_mul (σ⁻¹ * B)
    have hpt : ∀ x : ℝ,
        ‖shiftKernel Ψ σ t x‖ ≤ σ⁻¹ * B * (1 + ((x - t * σ) / σ) ^ 2)⁻¹ := by
      intro x
      rw [shiftKernel_norm hσ t x]
      have h1 : |Ψ ((x - t * σ) / σ)| ≤ B * (1 + ((x - t * σ) / σ) ^ 2)⁻¹ := by
        have h' := h.bound ((x - t * σ) / σ)
        rwa [div_eq_mul_inv] at h'
      calc σ⁻¹ * |Ψ ((x - t * σ) / σ)| ≤ σ⁻¹ * (B * (1 + ((x - t * σ) / σ) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = σ⁻¹ * B * (1 + ((x - t * σ) / σ) ^ 2)⁻¹ := by ring
    have hint : ∫ x : ℝ, σ⁻¹ * B * (1 + ((x - t * σ) / σ) ^ 2)⁻¹ = Real.pi * B := by
      rw [integral_const_mul, integral_inv_one_add_sq_shift σ t hσ]
      field_simp
    calc ∫ x, ‖shiftKernel Ψ σ t x‖
        ≤ ∫ x, σ⁻¹ * B * (1 + ((x - t * σ) / σ) ^ 2)⁻¹ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hIg
            (Filter.Eventually.of_forall hpt)
      _ = Real.pi * B := hint
  · intro σ t y hσ hy x
    have hhy : |y / σ| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hσ, div_le_iff₀ hσ]
      linarith
    have hL : ‖shiftKernel Ψ σ t (x - y) - shiftKernel Ψ σ t x‖
        = σ⁻¹ * |Ψ ((x - t * σ) / σ) - Ψ ((x - t * σ) / σ - y / σ)| := by
      rw [norm_shiftKernel_sub hσ t x y, abs_sub_comm]
    calc ‖shiftKernel Ψ σ t (x - y) - shiftKernel Ψ σ t x‖
        = σ⁻¹ * |Ψ ((x - t * σ) / σ) - Ψ ((x - t * σ) / σ - y / σ)| := hL
      _ ≤ σ⁻¹ * (|y / σ| * (4 * B / (1 + ((x - t * σ) / σ) ^ 2))) :=
          mul_le_mul_of_nonneg_left (abs_seed_sub_le h hhy) (by positivity)
      _ = (|y| / σ) * (4 * B / σ) * (1 + ((x - t * σ) / σ) ^ 2)⁻¹ := by
          rw [abs_div, abs_of_pos hσ]
          ring
  · intro σ t L hσ hL ht y x hy hx
    have hσne : σ ≠ 0 := hσ.ne'
    have hxabs : |x| ≤ 2 * |x - t * σ| := by
      have h1 : |t * σ| = |t| * σ := by rw [abs_mul, abs_of_pos hσ]
      have h2 : |t * σ| ≤ L := by rw [h1]; exact ht
      have h3 : L ≤ |x| / 2 := by linarith
      have h4 : |x| ≤ |x - t * σ| + |t * σ| := by
        calc |x| = |(x - t * σ) + t * σ| := by ring_nf
          _ ≤ |x - t * σ| + |t * σ| := abs_add_le _ _
      linarith
    have hxabs' : |x| ≤ 2 * |x - t * σ - y| := by
      have h1 : |t * σ| = |t| * σ := by rw [abs_mul, abs_of_pos hσ]
      have h2 : |t * σ + y| ≤ L + L / 2 := by
        have h5 : |t * σ + y| ≤ |t * σ| + |y| := abs_add_le _ _
        linarith
      have h3 : L + L / 2 ≤ |x| / 2 := by linarith
      have h4 : |x| ≤ |x - t * σ - y| + |t * σ + y| := by
        calc |x| = |(x - t * σ - y) + (t * σ + y)| := by ring_nf
          _ ≤ |x - t * σ - y| + |t * σ + y| := abs_add_le _ _
      linarith
    have key : ∀ w : ℝ, |x| ≤ 2 * |w| → |Ψ (w / σ)| ≤ 8 * B * (1 + (x / σ) ^ 2)⁻¹ := by
      intro w hw
      have h1 : 1 + (x / σ) ^ 2 ≤ 4 * (1 + (w / σ) ^ 2) := by
        apply one_add_sq_le_four_mul_of_two_mul
        rw [abs_div, abs_of_pos hσ, abs_div, abs_of_pos hσ]
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right hw hσ.le
      have h2 : (1 + (w / σ) ^ 2)⁻¹ ≤ 4 * (1 + (x / σ) ^ 2)⁻¹ := by
        have h' : (1 : ℝ) / (1 + (w / σ) ^ 2) ≤ 4 / (1 + (x / σ) ^ 2) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          linarith
        simpa [div_eq_mul_inv] using h'
      calc |Ψ (w / σ)| ≤ B / (1 + (w / σ) ^ 2) := h.bound _
        _ = B * (1 + (w / σ) ^ 2)⁻¹ := by ring
        _ ≤ B * (4 * (1 + (x / σ) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h2 hB
        _ ≤ 8 * B * (1 + (x / σ) ^ 2)⁻¹ := by
            have hnn : 0 ≤ (1 + (x / σ) ^ 2)⁻¹ := by positivity
            nlinarith [mul_nonneg hB hnn]
    have hL' : ‖shiftKernel Ψ σ t (x - y) - shiftKernel Ψ σ t x‖
        = σ⁻¹ * |Ψ ((x - t * σ - y) / σ) - Ψ ((x - t * σ) / σ)| := by
      have harg2 : (x - t * σ) / σ - y / σ = (x - t * σ - y) / σ := by
        ring
      rw [norm_shiftKernel_sub hσ t x y, harg2]
    calc ‖shiftKernel Ψ σ t (x - y) - shiftKernel Ψ σ t x‖
        = σ⁻¹ * |Ψ ((x - t * σ - y) / σ) - Ψ ((x - t * σ) / σ)| := hL'
      _ ≤ σ⁻¹ * (|Ψ ((x - t * σ - y) / σ)| + |Ψ ((x - t * σ) / σ)|) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h5 := abs_add_le (Ψ ((x - t * σ - y) / σ)) (-(Ψ ((x - t * σ) / σ)))
          simpa [sub_eq_add_neg] using h5
      _ ≤ σ⁻¹ * (8 * B * (1 + (x / σ) ^ 2)⁻¹ + 8 * B * (1 + (x / σ) ^ 2)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact add_le_add (key (x - t * σ - y) hxabs') (key (x - t * σ) hxabs)
      _ = 16 * B * σ⁻¹ * (1 + (x / σ) ^ 2)⁻¹ := by ring

end Work.Analysis.CzShift
