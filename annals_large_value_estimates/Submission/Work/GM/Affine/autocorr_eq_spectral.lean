import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.plancherel_continuous
import Submission.Work.GM.Affine.integrable_Fhat_sq

/-!
# The Wiener--Khinchin identity for the GM §9 test function

For a continuous compactly supported real function `F : ℝ → ℝ` and every `u : ℝ`,

  `∫ x, F x * F (x + u) = ∫ θ, ‖Fhat F θ‖ ^ 2 * cos (2 π θ u)`.

The proof is the classical one: the autocorrelation is the convolution `F ⋆ F̌` of the
complexification of `F` with its reflection, whose Fourier transform is
`Fhat F · conj (Fhat F) = ‖Fhat F‖² ∈ L¹` (the integrability is
`integrable_Fhat_sq`, a form of Plancherel).  Fourier inversion
(`Continuous.fourierInv_fourier_eq`) applied to that convolution then identifies the
autocorrelation with the inverse Fourier transform of `‖Fhat F‖²`; taking real parts gives
the cosine formula.
-/

namespace Work.GM.Affine

open MeasureTheory
open scoped FourierTransform

noncomputable section

/-- The complexification `x ↦ (F x : ℂ)` of a real function. -/
def Fcx (F : ℝ → ℝ) : ℝ → ℂ := fun x => (F x : ℂ)

/-- The complexified reflection `x ↦ (F (-x) : ℂ)`. -/
def Fref (F : ℝ → ℝ) : ℝ → ℂ := fun x => (F (-x) : ℂ)

/-- `Fhat F` is the Fourier transform of the complexification of `F`. -/
lemma Fhat_eq_fourier_Fcx (F : ℝ → ℝ) (ξ : ℝ) : Fhat F ξ = 𝓕 (Fcx F) ξ := rfl

/-- For a real-valued `F`, the Fourier transform of the reflection is the conjugate of the
Fourier transform of `F`. -/
lemma Fhat_neg_eq_conj (F : ℝ → ℝ) (ξ : ℝ) :
    Fhat F (-ξ) = (starRingEnd ℂ) (Fhat F ξ) := by
  simp only [Fhat, Real.fourier_eq]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Circle.smul_def, smul_eq_mul, map_mul, Complex.conj_ofReal,
    ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, inner_neg_right]

/-- The Fourier transform of the reflected complexification. -/
lemma fourier_Fref (F : ℝ → ℝ) (ξ : ℝ) : 𝓕 (Fref F) ξ = Fhat F (-ξ) := by
  have key := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) (Fcx F) ξ
  rw [show (⇑(LinearIsometryEquiv.neg ℝ) : ℝ → ℝ) = fun x => -x from rfl] at key
  rw [show (Fcx F) ∘ (fun x : ℝ => -x) = Fref F from rfl] at key
  rw [key]
  rfl

/-- The product of `Fhat F ξ` with its conjugate is the (real) square of the modulus. -/
lemma Fhat_mul_conj (F : ℝ → ℝ) (ξ : ℝ) :
    Fhat F ξ * Fhat F (-ξ) = ((‖Fhat F ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [Fhat_neg_eq_conj F ξ, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem autocorr_eq_spectral {F : ℝ → ℝ} (hF : Continuous F) (hcs : HasCompactSupport F) (u : ℝ) :
    (∫ x : ℝ, F x * F (x + u))
      = ∫ θ : ℝ, ‖Fhat F θ‖ ^ 2 * Real.cos (2 * Real.pi * θ * u) := by
  have hφc : Continuous (Fcx F) := Complex.continuous_ofReal.comp hF
  have hφcs : HasCompactSupport (Fcx F) := by
    simpa [HasCompactSupport, tsupport, Function.support, Fcx] using hcs
  have hφi : Integrable (Fcx F) := hφc.integrable_of_hasCompactSupport hφcs
  have hψc : Continuous (Fref F) := Complex.continuous_ofReal.comp (hF.comp continuous_neg)
  have hψcs : HasCompactSupport (Fref F) := by
    have h : HasCompactSupport (fun x : ℝ => F (-x)) := by
      have h' := hcs.comp_homeomorph (Homeomorph.neg ℝ)
      simpa [Function.comp_def] using h'
    simpa [HasCompactSupport, tsupport, Function.support, Fref] using h
  have hψi : Integrable (Fref F) := hψc.integrable_of_hasCompactSupport hψcs
  -- the autocorrelation, as the convolution of `Fcx F` with `Fref F`
  set A : ℝ → ℂ := convolution (Fcx F) (Fref F) (ContinuousLinearMap.mul ℂ ℂ) volume with hA
  have hAc : Continuous A := by
    rw [hA]
    exact hψcs.continuous_convolution_right (ContinuousLinearMap.mul ℂ ℂ)
      hφc.locallyIntegrable hψc
  have hAi : Integrable A := by
    rw [hA]
    exact hφi.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hψi
  -- its Fourier transform is `‖Fhat F‖²`
  have hFA_eq : 𝓕 A = fun ξ => ((‖Fhat F ξ‖ ^ 2 : ℝ) : ℂ) := by
    funext ξ
    rw [hA, Real.fourier_mul_convolution_eq hφi hψi ξ, fourier_Fref F ξ,
      show 𝓕 (Fcx F) ξ = Fhat F ξ from rfl, Fhat_mul_conj F ξ]
  have hFAi : Integrable (𝓕 A) := by
    rw [hFA_eq]
    exact (integrable_Fhat_sq hF hcs).ofReal
  -- Fourier inversion
  have hinv : A u = ∫ ξ : ℝ, Real.fourierChar (inner ℝ ξ u) • ((‖Fhat F ξ‖ ^ 2 : ℝ) : ℂ) := by
    have h := congrFun (Continuous.fourierInv_fourier_eq hAc hAi hFAi) u
    rw [Real.fourierInv_eq, hFA_eq] at h
    exact h.symm
  -- the real part of the left-hand side
  have hAre : (A u).re = ∫ x : ℝ, F x * F (x + u) := by
    have hint : Integrable (fun t : ℝ => F t * F (t - u)) := by
      have hcont : Continuous (fun t : ℝ => F t * F (t - u)) :=
        hF.mul (hF.comp (continuous_id.sub continuous_const))
      exact hcont.integrable_of_hasCompactSupport
        (hcs.mul_right (f' := fun t : ℝ => F (t - u)))
    have hAcu : A u = (((∫ t : ℝ, F t * F (t - u)) : ℝ) : ℂ) := by
      rw [hA, convolution_def]
      have hpt : ∀ t : ℝ, (ContinuousLinearMap.mul ℂ ℂ) (Fcx F t) (Fref F (u - t))
          = ((F t * F (t - u) : ℝ) : ℂ) := by
        intro t
        rw [ContinuousLinearMap.mul_apply', Fcx, Fref, neg_sub, Complex.ofReal_mul]
      rw [show (∫ t : ℝ, (ContinuousLinearMap.mul ℂ ℂ) (Fcx F t) (Fref F (u - t)))
            = ∫ t : ℝ, ((F t * F (t - u) : ℝ) : ℂ) from
          integral_congr_ae (Filter.Eventually.of_forall hpt)]
      exact ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hint
    have h2 : (∫ t : ℝ, F t * F (t - u)) = ∫ x : ℝ, F x * F (x + u) := by
      have key := MeasureTheory.integral_sub_right_eq_self (μ := volume)
        (fun t : ℝ => F (t + u) * F t) u
      simp only [sub_add_cancel] at key
      rw [key]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm (F (x + u)) (F x))
    rw [hAcu, Complex.ofReal_re, h2]
  -- the real part of the right-hand side
  have hBre : (∫ ξ : ℝ, Real.fourierChar (inner ℝ ξ u) • ((‖Fhat F ξ‖ ^ 2 : ℝ) : ℂ)).re
      = ∫ ξ : ℝ, ‖Fhat F ξ‖ ^ 2 * Real.cos (2 * Real.pi * ξ * u) := by
    have hFhat_cont : Continuous (Fhat F) := by
      have h : Continuous (FourierTransform.fourier (Fcx F)) :=
        VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
          (innerSL ℝ).continuous₂ hφi
      exact h
    have hcontB : Continuous (fun ξ : ℝ =>
        (Real.fourierChar (inner ℝ ξ u) : ℂ) * ((‖Fhat F ξ‖ ^ 2 : ℝ) : ℂ)) :=
      (continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const))).mul
        (Complex.continuous_ofReal.comp ((hFhat_cont.norm.pow 2)))
    have hintB : Integrable (fun ξ : ℝ =>
        Real.fourierChar (inner ℝ ξ u) • ((‖Fhat F ξ‖ ^ 2 : ℝ) : ℂ)) := by
      refine Integrable.mono' (integrable_Fhat_sq hF hcs) ?_ ?_
      · refine hcontB.aestronglyMeasurable.congr ?_
        filter_upwards with ξ
        rw [Circle.smul_def, smul_eq_mul]
      · filter_upwards with ξ
        rw [Circle.smul_def, smul_eq_mul, norm_mul]
        have h1 : ‖(Real.fourierChar (inner ℝ ξ u) : ℂ)‖ = 1 := Circle.norm_coe _
        rw [h1, one_mul]
        have h2 : ‖((‖Fhat F ξ‖ ^ 2 : ℝ) : ℂ)‖ = ‖Fhat F ξ‖ ^ 2 := by
          rw [show ‖((‖Fhat F ξ‖ ^ 2 : ℝ) : ℂ)‖ = |‖Fhat F ξ‖ ^ 2| from by simp]
          exact abs_of_nonneg (sq_nonneg _)
        rw [h2]
    have hpt : ∀ ξ : ℝ,
        (Real.fourierChar (inner ℝ ξ u) • ((‖Fhat F ξ‖ ^ 2 : ℝ) : ℂ)).re
          = ‖Fhat F ξ‖ ^ 2 * Real.cos (2 * Real.pi * ξ * u) := by
      intro ξ
      rw [Circle.smul_def, smul_eq_mul, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      have hfc : ((Real.fourierChar (inner ℝ ξ u) : ℂ)).re
          = Real.cos (2 * Real.pi * ξ * u) := by
        rw [Real.fourierChar_apply, Complex.exp_ofReal_mul_I_re, Real.inner_apply]
        congr 1
        ring
      rw [hfc]
      ring
    have hcomp : (∫ ξ : ℝ,
          (Real.fourierChar (inner ℝ ξ u) • ((‖Fhat F ξ‖ ^ 2 : ℝ) : ℂ)).re)
        = (∫ ξ : ℝ, Real.fourierChar (inner ℝ ξ u) • ((‖Fhat F ξ‖ ^ 2 : ℝ) : ℂ)).re := by
      simpa using Complex.reCLM.integral_comp_comm
        (φ := fun ξ : ℝ => Real.fourierChar (inner ℝ ξ u) • ((‖Fhat F ξ‖ ^ 2 : ℝ) : ℂ)) hintB
    rw [← hcomp]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have h := congrArg Complex.re hinv
  rw [hAre, hBre] at h
  exact h

end

end Work.GM.Affine
