import Mathlib
import Submission.Commons.Analysis.Complex.laplace_inversion_piecewise_C2
import Submission.Commons.Analysis.Complex.laplace_inversion_compact

namespace Commons.Analysis.Complex

open MeasureTheory intervalIntegral
open scoped FourierTransform RealInnerProductSpace

theorem laplace_transform_twisted_continuous_integrable {x₀ B : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B)
    {f : ℝ → ℂ} (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) (hf0 : f 0 = 0)
    {L : ℝ} (hL : 1 < L) {s : ℂ} (hs : 1 < s.re) {α : ℝ} (hα : α < s.re) :
    Continuous (fun τ : ℝ => ∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t) ∧
      MeasureTheory.Integrable (fun τ : ℝ => ∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t) := by
  have hLpos : 0 < L := by linarith
  have hgap : 0 < s.re - α := by linarith
  set c : ℝ := L * (s.re - α) with hc_def
  have hcpos : 0 < c := by rw [hc_def]; exact mul_pos hLpos hgap
  set h : ℝ → ℂ := fun u => Complex.exp (-(c:ℂ) * (u:ℂ)) * f (max 0 (min u x₀)) with hh
  -- `h` is continuous (clamped `f` times a decaying exponential)
  have hh_cont : Continuous h := by
    rw [hh]
    have hmem : ∀ u : ℝ, max 0 (min u x₀) ∈ Set.Icc (0:ℝ) x₀ :=
      fun u => ⟨le_max_left _ _, max_le hx₀.le (min_le_right _ _)⟩
    exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      (hcont.comp_continuous (continuous_const.max (continuous_id.min continuous_const)) hmem)
  -- `h` is supported in `[0, x₀]`
  have hh_supp : ∀ u : ℝ, u ∉ Set.Icc (0:ℝ) x₀ → h u = 0 := by
    intro u hu
    rw [Set.mem_Icc, not_and_or] at hu
    rcases hu with hu | hu
    · rw [not_le] at hu
      have hcl : max 0 (min u x₀) = 0 := by
        rw [min_eq_left (le_of_lt (lt_of_lt_of_le hu hx₀.le)), max_eq_left hu.le]
      simp only [hh]; rw [hcl, hf0, mul_zero]
    · rw [not_le] at hu
      have hcl : max 0 (min u x₀) = x₀ := by
        rw [min_eq_right hu.le, max_eq_right hx₀.le]
      simp only [hh]; rw [hcl, hvan x₀ le_rfl, mul_zero]
  have hh_cpt : HasCompactSupport h :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (fun u hu => by
      by_contra hmem; exact hu (hh_supp u hmem))
  have hh_int : MeasureTheory.Integrable h := hh_cont.integrable_of_hasCompactSupport hh_cpt
  have hFcont : Continuous (𝓕 h) := laplace_aux_continuous_fourier hh_int
  have hFint : MeasureTheory.Integrable (𝓕 h) := by
    rw [hh]
    exact laplace_aux_fourier_integrable hx₀ hcont hf2 ⟨B, hBnd⟩ hvan hf0 hcpos
  -- pointwise identity: the twisted integral is the Fourier transform of `h`
  have hpoint : ∀ τ : ℝ, (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
      = 𝓕 h ((L * (s.im - τ)) / (2 * Real.pi)) := by
    intro τ
    have hXY : (s - ((α:ℂ) + (τ:ℂ)*Complex.I)) * (L:ℂ)
        = (c:ℂ) + ((L*(s.im - τ) : ℝ) : ℂ) * Complex.I := by
      rw [hc_def]
      have hsz : s = (s.re : ℂ) + (s.im : ℂ) * Complex.I := (Complex.re_add_im s).symm
      conv_lhs => rw [hsz]
      push_cast
      ring
    have e1 : (∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
        = ∫ t in (0:ℝ)..x₀,
          Complex.exp (-(((c : ℂ) + ((L*(s.im - τ) : ℝ) : ℂ) * Complex.I) * (t : ℂ))) * f t := by
      apply intervalIntegral.integral_congr
      intro t _
      rw [hXY]
    rw [e1]
    rw [laplace_inner_eq_fourier hx₀ hvan hf0 (L * (s.im - τ))]
  have hG : (fun τ : ℝ => ∫ t in (0:ℝ)..x₀,
        Complex.exp (-(((s - ((α : ℂ) + (τ : ℂ) * Complex.I)) * (L : ℂ)) * (t : ℂ))) * f t)
      = fun τ : ℝ => 𝓕 h ((L * (s.im - τ)) / (2 * Real.pi)) := funext hpoint
  refine ⟨?_, ?_⟩
  · rw [hG]
    exact hFcont.comp (by fun_prop)
  · rw [hG]
    set a : ℝ := L / (2 * Real.pi) with ha_def
    set b : ℝ := L * s.im / (2 * Real.pi) with hb_def
    have ha : a ≠ 0 := by rw [ha_def]; positivity
    have h1 : MeasureTheory.Integrable (fun z : ℝ => 𝓕 h (-z)) := hFint.comp_neg
    have h2 : MeasureTheory.Integrable (fun y : ℝ => 𝓕 h (b - y)) := by
      have := h1.comp_sub_right b
      simpa only [neg_sub] using this
    have h3 : MeasureTheory.Integrable (fun τ : ℝ => 𝓕 h (b - a * τ)) := h2.comp_mul_left' ha
    have hkey : (fun τ : ℝ => 𝓕 h ((L * (s.im - τ)) / (2 * Real.pi)))
        = (fun τ : ℝ => 𝓕 h (b - a * τ)) := by
      funext τ
      rw [ha_def, hb_def]
      ring_nf
    rw [hkey]
    exact h3

end Commons.Analysis.Complex
