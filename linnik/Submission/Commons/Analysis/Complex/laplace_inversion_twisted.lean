import Mathlib
import Submission.Commons.Analysis.Complex.laplace_inversion_piecewise_C2

namespace Commons.Analysis.Complex

open MeasureTheory intervalIntegral
open scoped FourierTransform RealInnerProductSpace

theorem laplace_inversion_twisted {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0)
    {L : ℝ} (hL : 1 < L) {s : ℂ} (hs : 1 < s.re) {α : ℝ} (hα1 : 1 < α) (hασ : α < s.re)
    {m : ℕ} (hm : 2 ≤ m) :
    (∫ τ : ℝ, (m : ℂ) ^ (-(α : ℂ) - (τ : ℂ) * Complex.I) *
        (∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t))
      = (2 * (Real.pi : ℂ) / (L : ℂ)) * (m : ℂ) ^ (-s) * f (Real.log m / L) := by
  have hLpos : 0 < L := by linarith
  have hgap : 0 < s.re - α := by linarith
  set cL : ℝ := L * (s.re - α) with hcLdef
  set tL : ℝ := Real.log m / L with htLdef
  have hcLpos : 0 < cL := by rw [hcLdef]; exact mul_pos hLpos hgap
  have hmposR : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hlogm : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
  have htLpos : 0 < tL := by rw [htLdef]; exact div_pos hlogm hLpos
  have hmC : (m : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast m]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hmposR)
  have hlogC : Complex.log (m:ℂ) = (Real.log m : ℂ) := by
    rw [← Complex.ofReal_natCast m]
    exact (Complex.ofReal_log (le_of_lt hmposR)).symm
  -- inversion formula applied to `f` with real part `cL`, at the point `tL`
  let Φ : ℝ → ℂ := fun γ => (∫ u in (0:ℝ)..x₀,
        Complex.exp (-(((cL:ℂ) + (γ:ℂ) * Complex.I) * (u:ℂ))) * f u) *
        Complex.exp (((cL:ℂ) + (γ:ℂ) * Complex.I) * (tL:ℂ))
  have hInv : f tL = (1 / (2 * (Real.pi:ℂ))) * ∫ γ : ℝ, Φ γ := by
    have := laplace_inversion_piecewise_C2 (f := f) (x₀ := x₀) hx₀ hcont hf2 ⟨B, hBnd⟩
      hvan hf0 (c := cL) hcLpos tL htLpos
    simpa only [Φ] using this
  have hInvEq : (∫ γ : ℝ, Φ γ) = 2 * (Real.pi:ℂ) * f tL := by
    have h2pi : (2 * (Real.pi:ℂ)) ≠ 0 := by
      apply mul_ne_zero (by norm_num)
      exact_mod_cast Real.pi_ne_zero
    rw [hInv, one_div]
    rw [← mul_assoc, mul_inv_cancel₀ h2pi, one_mul]
  -- pointwise identity
  have hkey : ∀ τ : ℝ, (m:ℂ)^(-(α:ℂ) - (τ:ℂ) * Complex.I) *
        (∫ u in (0:ℝ)..x₀,
          Complex.exp (-(((s - ((α:ℂ) + (τ:ℂ) * Complex.I)) * (L:ℂ)) * (u:ℂ))) * f u)
      = (m:ℂ)^(-s) * Φ (L * s.im - L * τ) := by
    intro τ
    have hz : (s - ((α:ℂ) + (τ:ℂ) * Complex.I)) * (L:ℂ)
        = (cL:ℂ) + ((L * s.im - L * τ : ℝ):ℂ) * Complex.I := by
      rw [hcLdef]
      have hs' : s = (s.re:ℂ) + (s.im:ℂ) * Complex.I := (Complex.re_add_im s).symm
      conv_lhs => rw [hs']
      push_cast
      ring
    have hpow : (m:ℂ)^(-(α:ℂ) - (τ:ℂ) * Complex.I)
        = (m:ℂ)^(-s) * Complex.exp (((cL:ℂ) + ((L * s.im - L * τ : ℝ):ℂ) * Complex.I) * (tL:ℂ)) := by
      rw [show -(α:ℂ) - (τ:ℂ) * Complex.I
            = -s + (s - ((α:ℂ) + (τ:ℂ) * Complex.I)) by ring]
      rw [Complex.cpow_add (-s) (s - ((α:ℂ) + (τ:ℂ) * Complex.I)) hmC]
      have key : (m:ℂ)^(s - ((α:ℂ) + (τ:ℂ) * Complex.I))
          = Complex.exp (((cL:ℂ) + ((L * s.im - L * τ : ℝ):ℂ) * Complex.I) * (tL:ℂ)) := by
        rw [Complex.cpow_def_of_ne_zero hmC, hlogC]
        congr 1
        rw [hcLdef, htLdef]
        have hs' : s = (s.re:ℂ) + (s.im:ℂ) * Complex.I := (Complex.re_add_im s).symm
        have hLc : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hLpos)
        conv_lhs => rw [hs']
        push_cast
        field_simp
        ring
      rw [key]
    simp only [Φ]
    rw [hpow]
    have hinner : (∫ u in (0:ℝ)..x₀,
          Complex.exp (-(((s - ((α:ℂ) + (τ:ℂ) * Complex.I)) * (L:ℂ)) * (u:ℂ))) * f u)
        = (∫ u in (0:ℝ)..x₀,
          Complex.exp (-(((cL:ℂ) + ((L * s.im - L * τ : ℝ):ℂ) * Complex.I) * (u:ℂ))) * f u) := by
      apply intervalIntegral.integral_congr
      intro u _
      rw [hz]
    rw [hinner]
    ring
  -- change of variables in the outer integral
  have hcv : (∫ τ : ℝ, Φ (L * s.im - L * τ)) = (L:ℂ)⁻¹ * ∫ γ : ℝ, Φ γ := by
    have h := Measure.integral_comp_mul_left (fun y : ℝ => Φ (L * s.im - y)) L
    rw [h]
    rw [integral_sub_left_eq_self Φ volume (L * s.im)]
    rw [abs_of_pos (inv_pos.mpr hLpos)]
    rw [Complex.real_smul, Complex.ofReal_inv]
  calc
    (∫ τ : ℝ, (m : ℂ) ^ (-(α : ℂ) - (τ : ℂ) * Complex.I) *
        (∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t))
      = ∫ τ : ℝ, (m:ℂ)^(-s) * Φ (L * s.im - L * τ) :=
        integral_congr_ae (Filter.Eventually.of_forall hkey)
    _ = (m:ℂ)^(-s) * (∫ τ : ℝ, Φ (L * s.im - L * τ)) := by rw [MeasureTheory.integral_const_mul]
    _ = (m:ℂ)^(-s) * ((L:ℂ)⁻¹ * ∫ γ : ℝ, Φ γ) := by rw [hcv]
    _ = (m:ℂ)^(-s) * ((L:ℂ)⁻¹ * (2 * (Real.pi:ℂ) * f tL)) := by rw [hInvEq]
    _ = (2 * (Real.pi : ℂ) / (L : ℂ)) * (m : ℂ) ^ (-s) * f (Real.log m / L) := by
        rw [htLdef]
        ring

end Commons.Analysis.Complex
