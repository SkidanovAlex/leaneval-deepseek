import Submission.Commons.Measure.EuclideanSpace.integral_fderiv_mul_weighted_eq_neg
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

open MeasureTheory

namespace Commons.Measure.EuclideanSpace

noncomputable section

/-- **Weighted integration by parts, with only one compactly supported factor.**
For `F`, `G`, `φ : (Fin d → ℂ) → ℂ` of class `C¹` with `G` compactly supported, and any
direction `v`, the weighted derivative of `F` can be exchanged against that of `G` at the price
of a term involving the derivative of the weight `φ`:
`∫ (∂ᵥF) G e^{-φ} = - ∫ F (∂ᵥG) e^{-φ} + ∫ F G (∂ᵥφ) e^{-φ}`.

Contrary to `integral_fderiv_mul_weighted_eq_neg`, no compact-support hypothesis is placed on
`F`: the product `F G e^{-φ}` is compactly supported as soon as `G` is, and its total derivative
integrates to zero. -/
theorem integral_fderiv_mul_weighted_eq_neg_nocompact {d : ℕ} {F G φ : (Fin d → ℂ) → ℂ}
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) (hφ : ContDiff ℝ 1 φ)
    (hsG : HasCompactSupport G) (v : Fin d → ℂ) :
    MeasureTheory.integral MeasureTheory.volume
        (fun z => fderiv ℝ F z v * G z * Complex.exp (-(φ z)))
      = - MeasureTheory.integral MeasureTheory.volume
            (fun z => F z * fderiv ℝ G z v * Complex.exp (-(φ z)))
        + MeasureTheory.integral MeasureTheory.volume
            (fun z => F z * G z * fderiv ℝ φ z v * Complex.exp (-(φ z))) := by
  let A : (Fin d → ℂ) → ℂ := fun z => fderiv ℝ F z v * G z * Complex.exp (-(φ z))
  let B : (Fin d → ℂ) → ℂ := fun z => F z * fderiv ℝ G z v * Complex.exp (-(φ z))
  let C : (Fin d → ℂ) → ℂ := fun z => F z * G z * fderiv ℝ φ z v * Complex.exp (-(φ z))
  let hh : (Fin d → ℂ) → ℂ := fun z => F z * G z * Complex.exp (-(φ z))
  change (∫ z, A z) = -(∫ z, B z) + ∫ z, C z
  have hh_cd : ContDiff ℝ 1 hh := by
    show ContDiff ℝ 1 (fun z => F z * G z * Complex.exp (-(φ z)))
    exact (hF.mul hG).mul (hφ.neg.cexp)
  have hh_cs : HasCompactSupport hh := by
    show HasCompactSupport (fun z => F z * G z * Complex.exp (-(φ z)))
    exact (hsG.mul_left).mul_right
  have he_cs : HasCompactSupport (fun z : Fin d → ℂ => G z * Complex.exp (-(φ z))) :=
    hsG.mul_right
  have hGder_cs : HasCompactSupport (fun z : Fin d → ℂ => fderiv ℝ G z v * Complex.exp (-(φ z))) :=
    (hsG.fderiv_apply ℝ v).mul_right
  have hint_zero : ∫ z, fderiv ℝ hh z v = 0 :=
    integral_fderiv_apply_eq_zero (μ := volume) hh_cd hh_cs v
  have hderiv : ∀ z, fderiv ℝ hh z v = A z + B z - C z := by
    intro z
    have key := fderiv_mul_mul_cexp_neg_apply (F := F) (G := G) (φ := φ) (x := z)
      (hF.differentiable_one.differentiableAt) (hG.differentiable_one.differentiableAt)
      (hφ.differentiable_one.differentiableAt) v
    simp only [A, B, C, hh] at key ⊢
    exact key
  have hAint : Integrable A := by
    apply Continuous.integrable_of_hasCompactSupport
    · show Continuous (fun z => fderiv ℝ F z v * G z * Complex.exp (-(φ z)))
      have h1 : Continuous (fun z => fderiv ℝ F z v) :=
        (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
      exact (h1.mul hG.continuous).mul (hφ.neg.cexp.continuous)
    · apply HasCompactSupport.mono he_cs
      intro z
      simp only [Function.mem_support, ne_eq]
      intro hz h
      exact hz (by
        have h1 : (fderiv ℝ F z v) * G z * Complex.exp (-(φ z))
            = (fderiv ℝ F z v) * (G z * Complex.exp (-(φ z))) := by ring
        simp only [A]
        rw [h1, h, mul_zero])
  have hBint : Integrable B := by
    apply Continuous.integrable_of_hasCompactSupport
    · show Continuous (fun z => F z * fderiv ℝ G z v * Complex.exp (-(φ z)))
      have h1 : Continuous (fun z => fderiv ℝ G z v) :=
        (hG.continuous_fderiv (by norm_num)).clm_apply continuous_const
      exact (hF.continuous.mul h1).mul (hφ.neg.cexp.continuous)
    · apply HasCompactSupport.mono hGder_cs
      intro z
      simp only [Function.mem_support, ne_eq]
      intro hz h
      exact hz (by
        have h1 : F z * (fderiv ℝ G z v) * Complex.exp (-(φ z))
            = F z * ((fderiv ℝ G z v) * Complex.exp (-(φ z))) := by ring
        simp only [B]
        rw [h1, h, mul_zero])
  have hCint : Integrable C := by
    apply Continuous.integrable_of_hasCompactSupport
    · show Continuous (fun z => F z * G z * fderiv ℝ φ z v * Complex.exp (-(φ z)))
      have h1 : Continuous (fun z => fderiv ℝ φ z v) :=
        (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
      exact ((hF.continuous.mul hG.continuous).mul h1).mul (hφ.neg.cexp.continuous)
    · apply HasCompactSupport.mono he_cs
      intro z
      simp only [Function.mem_support, ne_eq]
      intro hz h
      exact hz (by
        have h1 : F z * G z * (fderiv ℝ φ z v) * Complex.exp (-(φ z))
            = (F z * (fderiv ℝ φ z v)) * (G z * Complex.exp (-(φ z))) := by ring
        simp only [C]
        rw [h1, h, mul_zero])
  have hAB_zero : ∫ z, (A z + B z - C z) = 0 := by
    have heq : (fun z => fderiv ℝ hh z v) = fun z => A z + B z - C z :=
      funext fun z => hderiv z
    rw [← heq]
    exact hint_zero
  have hsplit : ∫ z, (A z + B z - C z) = (∫ z, A z) + (∫ z, B z) - (∫ z, C z) := by
    rw [integral_sub (f := fun z => A z + B z) (g := C) (hAint.add hBint) hCint,
        integral_add hAint hBint]
  rw [hsplit] at hAB_zero
  linear_combination hAB_zero

end

end Commons.Measure.EuclideanSpace
