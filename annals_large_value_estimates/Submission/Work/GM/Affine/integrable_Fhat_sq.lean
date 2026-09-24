import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.plancherel_continuous

/-!
# Integrability of `‖Fhat f‖²` for continuous compactly supported `f`

GM §9 uses the test function `f : ℝ → ℝ`, continuous with compact support, and needs
`y ↦ ‖Fhat f y‖²` to be integrable on `ℝ` (this is Plancherel: the Fourier transform of an
`L¹ ∩ L²` function lies in `L²`).

We prove it for an arbitrary continuous compactly supported complex-valued `g` and specialise.
The argument uses the Plancherel identity `plancherel_continuous` (already available in this
directory): `∫ ‖g‖² = ∫ ‖𝓕 g‖²`.  Writing both sides as `toReal` of the corresponding
`lintegral` (legitimate since the integrands are nonnegative and measurable), the equality reads
`A = B.toReal`.  If `B = ⊤` then `A = 0`, hence `g = 0` a.e. and `𝓕 g = 0`; otherwise `B < ∞`
gives `HasFiniteIntegral` of `‖𝓕 g‖²` directly.
-/

namespace Work.GM.Affine

open MeasureTheory
open scoped FourierTransform

/-- **Plancherel, integrability form.** For a continuous compactly supported
`g : ℝ → ℂ`, the square of the modulus of its Fourier transform is integrable. -/
lemma integrable_fourier_sq_of_continuous_hasCompactSupport {g : ℝ → ℂ} (hg : Continuous g)
    (hcs : HasCompactSupport g) :
    Integrable (fun y : ℝ => ‖FourierTransform.fourier g y‖ ^ 2) := by
  have hgint : Integrable g := hg.integrable_of_hasCompactSupport hcs
  have hFcont : Continuous (FourierTransform.fourier g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hgint
  have hplan : ∫ x, ‖g x‖ ^ 2 = ∫ ξ, ‖FourierTransform.fourier g ξ‖ ^ 2 :=
    plancherel_continuous g hg hcs
  have hAeq : ∫ x, ‖g x‖ ^ 2
      = (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg _)
      (hg.norm.pow 2).aestronglyMeasurable
  have hBeq : ∫ ξ, ‖FourierTransform.fourier g ξ‖ ^ 2
      = (∫⁻ ξ, ENNReal.ofReal (‖FourierTransform.fourier g ξ‖ ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg _)
      (hFcont.norm.pow 2).aestronglyMeasurable
  by_cases htop : (∫⁻ ξ, ENNReal.ofReal (‖FourierTransform.fourier g ξ‖ ^ 2)) = ⊤
  · -- degenerate case: the `L²`-mass of `𝓕 g` is infinite, which forces `g = 0`
    have hA0 : ∫ x, ‖g x‖ ^ 2 = 0 := by rw [hplan, hBeq, htop, ENNReal.toReal_top]
    have hint : Integrable (fun x : ℝ => ‖g x‖ ^ 2) :=
      MemLp.integrable_norm_pow (hg.memLp_of_hasCompactSupport hcs) (by norm_num)
    have hzero : (fun x : ℝ => ‖g x‖ ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg _) hint).1 hA0
    have hg0 : g =ᵐ[volume] 0 := by
      filter_upwards [hzero] with x hx
      exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).1 (by simpa using hx)
    have hfun : (fun y : ℝ => ‖FourierTransform.fourier g y‖ ^ 2) = 0 := by
      funext y
      rw [Real.fourier_congr_ae hg0 y]
      simp [Real.fourier_eq]
    rw [hfun]
    exact integrable_zero ℝ ℝ volume
  · -- non-degenerate case: finite `lintegral` gives `HasFiniteIntegral`
    have hBlt : (∫⁻ ξ, ENNReal.ofReal (‖FourierTransform.fourier g ξ‖ ^ 2)) < ⊤ :=
      lt_top_iff_ne_top.2 htop
    refine ⟨(hFcont.norm.pow 2).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => sq_nonneg _)).2 hBlt

theorem integrable_Fhat_sq {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    MeasureTheory.Integrable (fun y : ℝ => (‖Work.GM.Affine.Fhat f y‖ : ℝ) ^ 2) := by
  have hgc : Continuous (fun u : ℝ => (f u : ℂ)) := Complex.continuous_ofReal.comp hf
  have hgcs : HasCompactSupport (fun u : ℝ => (f u : ℂ)) := by
    simpa [HasCompactSupport, tsupport, Function.support] using hcs
  have h := integrable_fourier_sq_of_continuous_hasCompactSupport hgc hgcs
  simpa [Fhat] using h

end Work.GM.Affine
