import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Separation.CompletelyRegular

open MeasureTheory

namespace Commons.Measure.EuclideanSpace

noncomputable section

/-- The Fréchet derivative of `z ↦ Complex.exp (-(φ z))` is multiplication by
`Complex.exp (-(φ z))` composed with `-(fderiv ℝ φ z)`. -/
lemma fderiv_cexp_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℂ} {x : E} (hφ : DifferentiableAt ℝ φ x) :
    fderiv ℝ (fun z => Complex.exp (-(φ z))) x
      = Complex.exp (-(φ x)) • (-(fderiv ℝ φ x)) := by
  have hneg : HasFDerivAt (fun z => -(φ z)) (-(fderiv ℝ φ x)) x := hφ.hasFDerivAt.neg
  exact hneg.cexp.fderiv

/-- **Leibniz rule** for the product `F * G * exp (-φ)`, evaluated on a direction `v`.

If `F`, `G` and `φ` are differentiable at `x`, then the directional derivative of
`z ↦ F z * G z * exp (-(φ z))` at `x` along `v` is
`(∂ᵥF) G e^{-φ} + F (∂ᵥG) e^{-φ} - F G (∂ᵥφ) e^{-φ}`. -/
lemma fderiv_mul_mul_cexp_neg_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G φ : E → ℂ} {x : E} (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x)
    (hφ : DifferentiableAt ℝ φ x) (v : E) :
    fderiv ℝ (fun z => F z * G z * Complex.exp (-(φ z))) x v
      = (fderiv ℝ F x v) * G x * Complex.exp (-(φ x))
        + F x * (fderiv ℝ G x v) * Complex.exp (-(φ x))
        - F x * G x * (fderiv ℝ φ x v) * Complex.exp (-(φ x)) := by
  have hFG : DifferentiableAt ℝ (fun z => F z * G z) x := hF.mul hG
  have he : DifferentiableAt ℝ (fun z => Complex.exp (-(φ z))) x := hφ.neg.cexp
  have hf_cexp : fderiv ℝ (fun z => Complex.exp (-(φ z))) x
      = Complex.exp (-(φ x)) • (-(fderiv ℝ φ x)) := fderiv_cexp_neg hφ
  have hmul : fderiv ℝ (fun z => F z * G z * Complex.exp (-(φ z))) x
      = (F x * G x) • (Complex.exp (-(φ x)) • (-(fderiv ℝ φ x)))
        + Complex.exp (-(φ x)) • (F x • fderiv ℝ G x + G x • fderiv ℝ F x) := by
    change fderiv ℝ ((fun z => F z * G z) * (fun z => Complex.exp (-(φ z)))) x = _
    rw [fderiv_mul hFG he,
        show fderiv ℝ (fun z => F z * G z) x = F x • fderiv ℝ G x + G x • fderiv ℝ F x
          from fderiv_mul hF hG,
        hf_cexp]
  rw [hmul]
  simp only [add_apply, smul_apply, neg_apply, smul_eq_mul]
  ring

/-- The integral of any directional derivative `z ↦ fderiv ℝ h z v` of a compactly supported
`C¹` complex-valued function `h` on a finite-dimensional real normed space vanishes.

This is integration by parts against the constant function `1`. -/
lemma integral_fderiv_apply_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [MeasureTheory.Measure.IsAddHaarMeasure μ]
    {h : E → ℂ} (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) (v : E) :
    ∫ z, fderiv ℝ h z v ∂μ = 0 := by
  have hint : Integrable (fun z => fderiv ℝ h z v) μ := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hh.continuous_fderiv (by norm_num)).clm_apply continuous_const
    · exact hs.fderiv_apply ℝ v
  have hfg' : Integrable (fun x : E => (1:ℂ) * fderiv ℝ h x v) μ := by simpa using hint
  have hf'g : Integrable (fun x : E => fderiv ℝ (fun _ : E => (1:ℂ)) x v * h x) μ := by
    have hzero : (fun x : E => fderiv ℝ (fun _ : E => (1:ℂ)) x v * h x) = fun _ => 0 := by
      funext x; simp
    rw [hzero]; exact integrable_zero _ _ _
  have hfg : Integrable (fun x : E => (1:ℂ) * h x) μ := by
    simpa using (hh.continuous.integrable_of_hasCompactSupport hs)
  have hmain := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := μ) (f := fun _ : E => (1:ℂ)) (g := h) (v := v)
    hf'g hfg' hfg
    (fun x _ => differentiableAt_const (1:ℂ))
    (fun x _ => hh.differentiable_one.differentiableAt)
  simp only [one_mul] at hmain
  rw [hmain]
  simp

/-- **Weighted integration by parts.**
For `F`, `G`, `φ : (Fin d → ℂ) → ℂ` of class `C¹` with `F`, `G` compactly supported, and any
direction `v`, the weighted derivative of `F` can be exchanged against that of `G` at the price
of a term involving the derivative of the weight `φ`:
`∫ (∂ᵥF) G e^{-φ} = - ∫ F (∂ᵥG) e^{-φ} + ∫ F G (∂ᵥφ) e^{-φ}`.

This is the integration by parts identity `∫ ∂ᵥ(F G e^{-φ}) = 0` (the total derivative of a
compactly supported function integrates to zero) together with the Leibniz rule. -/
theorem integral_fderiv_mul_weighted_eq_neg {d : ℕ} {F G φ : (Fin d → ℂ) → ℂ}
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G) (hφ : ContDiff ℝ 1 φ)
    (hsF : HasCompactSupport F) (hsG : HasCompactSupport G) (v : Fin d → ℂ) :
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
    exact (hsF.mul_right).mul_right
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