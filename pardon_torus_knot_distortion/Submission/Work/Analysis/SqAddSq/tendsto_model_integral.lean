import Mathlib
import Submission.Work.Smooth.JordanSeparation.Defs

/-!
# The model integral of Pardon's distortion estimate

This file computes the limit, as `s → 0⁺`, of the model integral

`∫ τ in (0,ε), (s * γ'(0)) / (γ'(0)² τ² + s² · u₀²)`,  where `u₀ = unitTangent c 0`.

Writing `γ'(0) = r·u₀` with `r = ‖γ'(0)‖ > 0` and `u₀` a unit complex number the integrand
collapses to `conj u₀ · (s r / (r² τ² + s²))`, and the elementary antiderivative gives

`∫ τ in (0,ε), s r / (r² τ² + s²) = arctan (ε r / s) → π/2  (s → 0⁺)`.

Hence the limit is `(π/2) · conj u₀ = (π/2) · unitTangent c 0` (the conjugate of a unit complex
number being its inverse).
-/

namespace Work.Analysis.SqAddSq

/-- The antiderivative of `τ ↦ s/(A τ² + s²)` on `[0, ε]`, for `A > 0`, `s > 0`. -/
lemma integral_s_div_sq_add_sq_local {A s ε : ℝ} (hA : 0 < A) (hs : 0 < s) (_hε : 0 ≤ ε) :
    ∫ τ in (0 : ℝ)..ε, s / (A * τ ^ 2 + s ^ 2)
      = (1 / Real.sqrt A) * Real.arctan (ε * Real.sqrt A / s) := by
  have hApos : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hderiv : ∀ τ : ℝ,
      HasDerivAt (fun τ : ℝ => (1 / Real.sqrt A) * Real.arctan (τ * (Real.sqrt A / s)))
        (s / (A * τ ^ 2 + s ^ 2)) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ : ℝ => τ * (Real.sqrt A / s)) (Real.sqrt A / s) τ := by
      simpa [div_eq_mul_inv, mul_assoc] using (hasDerivAt_id τ).mul_const (Real.sqrt A / s)
    have h2' := (Real.hasDerivAt_arctan (τ * (Real.sqrt A / s))).comp τ h1
    have h2 : HasDerivAt (fun τ : ℝ => Real.arctan (τ * (Real.sqrt A / s)))
        (Real.sqrt A * s / (A * τ ^ 2 + s ^ 2)) τ := by
      refine h2'.congr_deriv ?_
      have hsq : (τ * (Real.sqrt A / s)) ^ 2 = A * τ ^ 2 / s ^ 2 := by
        rw [mul_pow, div_pow, Real.sq_sqrt hA.le]; ring
      rw [hsq]
      have hden : A * τ ^ 2 + s ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    refine (h2.const_mul (1 / Real.sqrt A)).congr_deriv ?_
    have hden : A * τ ^ 2 + s ^ 2 ≠ 0 := by positivity
    field_simp
  have hcont : Continuous fun τ : ℝ => s / (A * τ ^ 2 + s ^ 2) := by
    apply Continuous.div continuous_const _ (fun τ => ?_)
    · fun_prop
    · positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
        (hcont.intervalIntegrable _ _)]
  rw [zero_mul, Real.arctan_zero, mul_zero, sub_zero,
      show ε * (Real.sqrt A / s) = ε * Real.sqrt A / s by ring]

/-- The integrand of the model integral, rewritten in terms of the unit tangent direction.
If `u` is a unit complex number and `γ'(0) = r·u` with `r ≥ 0`, then for `s > 0`
`(s γ'(0))/(γ'(0)² τ² + s² u²) = conj u · (s r/(r² τ² + s²))`. -/
lemma integrand_complex_eq (u : ℂ) (hu : ‖u‖ = 1) (r τ s : ℝ) (hs : 0 < s) :
    (s : ℂ) * ((r : ℂ) * u) / (((r : ℂ) * u) ^ 2 * (τ : ℂ) ^ 2 + (s : ℂ) ^ 2 * u ^ 2)
      = (starRingEnd ℂ u) * ((s * r / (r ^ 2 * τ ^ 2 + s ^ 2) : ℝ) : ℂ) := by
  have hu0 : u ≠ 0 := by
    intro h; rw [h, norm_zero] at hu; norm_num at hu
  have hunit : u * (starRingEnd ℂ u) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; norm_num
  have hD : r ^ 2 * τ ^ 2 + s ^ 2 ≠ 0 := by positivity
  have hnum : (s : ℂ) * ((r : ℂ) * u) = ((s * r : ℝ) : ℂ) * u := by push_cast; ring
  have hden : ((r : ℂ) * u) ^ 2 * (τ : ℂ) ^ 2 + (s : ℂ) ^ 2 * u ^ 2
      = u ^ 2 * ((r ^ 2 * τ ^ 2 + s ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have key : u⁻¹ = (starRingEnd ℂ u) := inv_eq_of_mul_eq_one_right hunit
  rw [hnum, hden, mul_comm (u ^ 2) _, ← key, Complex.ofReal_div]
  field_simp

theorem tendsto_model_integral (c : Work.Smooth.Jordan.SmoothPlaneCurve)
    (h : Work.Smooth.Jordan.SmoothPlaneCurve.IsImmersion c) {ε : ℝ} (hε : 0 < ε) :
    Filter.Tendsto (fun s : ℝ => ∫ τ in (0 : ℝ)..ε,
        (s : ℂ) * deriv c.γ 0 /
          ((deriv c.γ 0) ^ 2 * (τ : ℂ) ^ 2
            + (s : ℂ) ^ 2 * (Work.Smooth.JordanSeparation.unitTangent c 0) ^ 2))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((Real.pi / 2 : ℂ) * (starRingEnd ℂ) (Work.Smooth.JordanSeparation.unitTangent c 0))) := by
  set u := Work.Smooth.JordanSeparation.unitTangent c 0 with hu
  set d := deriv c.γ 0 with hd
  have hdne : d ≠ 0 := by rw [hd]; exact h 0
  set r := ‖d‖ with hr
  have hrpos : 0 < r := by rw [hr]; exact norm_pos_iff.mpr hdne
  have hur : ‖u‖ = 1 := by
    rw [hu]; exact Work.Smooth.JordanSeparation.norm_unitTangent c h 0
  have hd_eq : d = (r : ℂ) * u := by
    have hc : ((r : ℂ)) ≠ 0 := by rw [Complex.ofReal_ne_zero]; exact ne_of_gt hrpos
    have hthis : u = d / ((r : ℝ) : ℂ) := by
      rw [hu, Work.Smooth.JordanSeparation.unitTangent_def, ← hd, ← hr]
    rw [hthis]
    exact (mul_div_cancel₀ d hc).symm
  have hmain : ∀ s : ℝ, 0 < s →
      (∫ τ in (0 : ℝ)..ε, (s : ℂ) * d / (d ^ 2 * (τ : ℂ) ^ 2 + (s : ℂ) ^ 2 * u ^ 2))
        = (starRingEnd ℂ u) * ((Real.arctan (ε * r / s) : ℝ) : ℂ) := by
    intro s hs
    have hpt : ∀ τ : ℝ, (s : ℂ) * d / (d ^ 2 * (τ : ℂ) ^ 2 + (s : ℂ) ^ 2 * u ^ 2)
        = (starRingEnd ℂ u) * ((s * r / (r ^ 2 * τ ^ 2 + s ^ 2) : ℝ) : ℂ) := by
      intro τ
      rw [hd_eq]
      exact integrand_complex_eq u hur r τ s hs
    rw [intervalIntegral.integral_congr (fun τ _ => hpt τ)]
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_ofReal]
    rw [show (∫ τ in (0 : ℝ)..ε, s * r / (r ^ 2 * τ ^ 2 + s ^ 2))
          = r * ∫ τ in (0 : ℝ)..ε, s / (r ^ 2 * τ ^ 2 + s ^ 2) by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro τ _
      rw [mul_comm s r]
      exact mul_div_assoc r s _]
    rw [integral_s_div_sq_add_sq_local (by positivity) hs hε.le]
    rw [Real.sqrt_sq hrpos.le, ← mul_assoc, mul_one_div_cancel (ne_of_gt hrpos), one_mul]
  have hlim : Filter.Tendsto (fun s : ℝ => Real.arctan (ε * r / s))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Real.pi / 2)) := by
    have hk : 0 < ε * r := mul_pos hε hrpos
    have h1 : Filter.Tendsto (fun s : ℝ => s⁻¹) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        Filter.atTop := tendsto_inv_nhdsGT_zero
    have h2 : Filter.Tendsto (fun s : ℝ => (ε * r) * s⁻¹) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        Filter.atTop := h1.const_mul_atTop hk
    have h3 : Filter.Tendsto (fun s : ℝ => ε * r / s) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        Filter.atTop := by simpa [div_eq_mul_inv] using h2
    exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h3
  have hH : Filter.Tendsto
      (fun s : ℝ => (starRingEnd ℂ u) * ((Real.arctan (ε * r / s) : ℝ) : ℂ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((Real.pi / 2 : ℂ) * (starRingEnd ℂ u))) := by
    have h1 : Filter.Tendsto (fun s : ℝ => ((Real.arctan (ε * r / s) : ℝ) : ℂ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (((Real.pi / 2 : ℝ)) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (Real.pi / 2)).comp hlim
    have h2 := h1.const_mul (starRingEnd ℂ u)
    have heq : (starRingEnd ℂ u) * (((Real.pi / 2 : ℝ)) : ℂ)
        = (Real.pi / 2 : ℂ) * (starRingEnd ℂ u) := by
      rw [Complex.ofReal_div, Complex.ofReal_ofNat]
      ring
    rw [← heq]
    exact h2
  refine hH.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (hmain s hs).symm

end Work.Analysis.SqAddSq
