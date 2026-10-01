import Mathlib
import Submission.Commons.Analysis.Complex.laplace_bound_two_sided

open Complex DirichletCharacter Metric Filter Set Topology MeasureTheory
open scoped Real Topology BigOperators

set_option autoImplicit false

namespace Commons.NumberTheory.Linnik

/-- **The key geometric fact of HB (6.14).**  If `|1 - β₁| ≤ δ` and
`δ < ‖1 - β₁ + iγ'‖`, then `|γ'| > δ/2`: otherwise `‖1 - β₁ + iγ'‖ ≤ |1-β₁| + |γ'| ≤ δ`. -/
theorem gt_half_delta_of_far {δ β₁ γ' lam₁ L : ℝ} (hL : 0 < L) (h1 : |1 - β₁| ≤ lam₁ / L)
    (hlam : lam₁ ≤ δ * L / 2)
    (h2 : δ < ‖(1:ℂ) - (β₁ : ℂ) + (γ' : ℂ) * Complex.I‖) : δ / 2 < |γ'| := by
  by_contra h
  push Not at h
  have h3 : ‖(1:ℂ) - (β₁ : ℂ) + (γ' : ℂ) * Complex.I‖ ≤ |1 - β₁| + |γ'| := by
    have hsplit : (1:ℂ) - (β₁ : ℂ) + (γ' : ℂ) * Complex.I =
        (((1 - β₁ : ℝ)) : ℂ) + (((γ' : ℝ)) : ℂ) * Complex.I := by push_cast; ring
    rw [hsplit]
    calc ‖(((1 - β₁ : ℝ)) : ℂ) + (((γ' : ℝ)) : ℂ) * Complex.I‖
        ≤ ‖(((1 - β₁ : ℝ)) : ℂ)‖ + ‖(((γ' : ℝ)) : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |1 - β₁| + |γ'| := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one,
            Complex.norm_real, Real.norm_eq_abs]
  have h4 : lam₁ / L ≤ δ / 2 := by
    rw [div_le_iff₀ hL]
    linarith
  linarith

/-- **The decay of `F` far from the zero (HB (6.14)).**  For `z = a + iη` with `|a| ≤ M` and
`|η| ≥ (δ/2)L`, the two-sided Laplace bound gives
`‖F(z)‖ ≤ ‖f 0‖/((δ/2)L) + (2‖f'(0⁺)‖ + 2Bx₀)e^{x₀M}/((δ/2)L)²`. -/
theorem laplace_far_le {x₀ B M δ L : ℝ} (hx₀ : 0 < x₀) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hL : 0 < L) {f : ℝ → ℂ}
    (hcont : ContinuousOn f (Set.Icc 0 x₀)) (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B)
    (hvan : ∀ t : ℝ, x₀ ≤ t → f t = 0) {a η : ℝ} (ha : |a| ≤ M)
    (hη : δ / 2 * L ≤ |η|) :
    ‖∫ t in (0:ℝ)..x₀, Complex.exp (-(((((a : ℂ) + (η : ℂ) * Complex.I))) * (t : ℂ))) * f t‖
      ≤ ‖f 0‖ / (δ / 2 * L)
        + (2 * ‖derivWithin f (Set.Ioi 0) 0‖ + 2 * B * x₀) * Real.exp (x₀ * M)
            / (δ / 2 * L) ^ 2 := by
  set z : ℂ := (a : ℂ) + (η : ℂ) * Complex.I with hzdef
  have hzre : z.re = a := by rw [hzdef]; simp
  have hzim : z.im = η := by rw [hzdef]; simp
  have hzpos : 0 < ‖z‖ := by
    have h1 : |η| ≤ ‖z‖ := by
      rw [← hzim]
      exact Complex.abs_im_le_norm z
    have h2 : 0 < δ / 2 * L := by positivity
    linarith
  have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
  have hmain := Commons.Analysis.Complex.laplace_bound_two_sided hx₀ hB hcont hf2 hBnd hvan hz0
  have hexp : Real.exp (x₀ * |z.re|) ≤ Real.exp (x₀ * M) := by
    apply Real.exp_le_exp.mpr
    rw [hzre]
    exact mul_le_mul_of_nonneg_left ha hx₀.le
  have hzge : δ / 2 * L ≤ ‖z‖ := by
    have h1 : |η| ≤ ‖z‖ := by
      rw [← hzim]; exact Complex.abs_im_le_norm z
    linarith
  have hdpos : 0 < δ / 2 * L := by positivity
  have h1 : ‖f 0‖ / ‖z‖ ≤ ‖f 0‖ / (δ / 2 * L) :=
    div_le_div_of_nonneg_left (norm_nonneg _) hdpos hzge
  have h2 : (2 * ‖derivWithin f (Set.Ioi 0) 0‖ + 2 * B * x₀) * Real.exp (x₀ * |z.re|) / ‖z‖ ^ 2
      ≤ (2 * ‖derivWithin f (Set.Ioi 0) 0‖ + 2 * B * x₀) * Real.exp (x₀ * M) / (δ / 2 * L) ^ 2 := by
    have hc : 0 ≤ (2 * ‖derivWithin f (Set.Ioi 0) 0‖ + 2 * B * x₀) := by positivity
    have hnum : (2 * ‖derivWithin f (Set.Ioi 0) 0‖ + 2 * B * x₀) * Real.exp (x₀ * |z.re|)
        ≤ (2 * ‖derivWithin f (Set.Ioi 0) 0‖ + 2 * B * x₀) * Real.exp (x₀ * M) :=
      mul_le_mul_of_nonneg_left hexp hc
    have hden : (δ / 2 * L) ^ 2 ≤ ‖z‖ ^ 2 := by
      apply sq_le_sq'
      · linarith [norm_nonneg z]
      · exact hzge
    calc (2 * ‖derivWithin f (Set.Ioi 0) 0‖ + 2 * B * x₀) * Real.exp (x₀ * |z.re|) / ‖z‖ ^ 2
        ≤ (2 * ‖derivWithin f (Set.Ioi 0) 0‖ + 2 * B * x₀) * Real.exp (x₀ * M) / ‖z‖ ^ 2 :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (2 * ‖derivWithin f (Set.Ioi 0) 0‖ + 2 * B * x₀) * Real.exp (x₀ * M) / (δ / 2 * L) ^ 2 :=
          div_le_div_of_nonneg_left (mul_nonneg hc (Real.exp_nonneg _)) (by positivity) hden
  have hz' : (∫ t in (0:ℝ)..x₀, Complex.exp (-(z * (t : ℂ))) * f t)
      = ∫ t in (0:ℝ)..x₀, Complex.exp (-(((((a : ℂ) + (η : ℂ) * Complex.I))) * (t : ℂ))) * f t := by
    rw [hzdef]
  rw [hz'] at hmain
  linarith [hmain, h1, h2]

end Commons.NumberTheory.Linnik
