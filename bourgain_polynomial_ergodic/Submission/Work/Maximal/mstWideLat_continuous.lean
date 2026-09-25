import Mathlib
import Submission.Work.Maximal.mstWideLat_defs
import Submission.Work.Maximal.mstWideLat_integrable

/-!
# Continuity of the band-limited interpolant of the wide-bump multiplier (MST Theorem 1, Half 2)

This module proves that the band-limited interpolant `mstWideLat P χ η s F T = 𝓕⁻ (mstWideExt)`
is a *continuous* function on `ℝ`.  The reason is soft: the amplitude `mstWideExt` is `C²` with
compact support, in particular integrable, and the inverse Fourier transform
`𝓕⁻ g = ∫ ξ, e^{2πi x ξ} g ξ dξ` of an integrable function is continuous by dominated convergence
(`VectorFourier.fourierIntegral_continuous`).

Continuity is what makes the "lattice sampling principle" applicable downstream: the curve identity
`mstWideLat_curve` evaluates `mstWideLat` at the moving points `-(n : ℝ) - P(N u)`, and the maximal
function comparison samples the continuous function `mstWideLat` along the curve, so it must at
least be continuous.
-/

namespace Work.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal FourierTransform

noncomputable section

/-- The Fourier transform of an integrable function on `ℝ` is continuous
(dominated convergence: `VectorFourier.fourierIntegral_continuous`). -/
private lemma continuous_fourier_of_integrable {g : ℝ → ℂ} (hg : MeasureTheory.Integrable g) :
    Continuous (𝓕 g) := by
  have hc : Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hg
  convert hc using 1
  all_goals
    funext w
    rw [Real.fourier_eq]
    simp only [VectorFourier.fourierIntegral]
    congr 1

/-- The inverse Fourier transform of an integrable function on `ℝ` is continuous. -/
private lemma continuous_fourierInv_of_integrable {g : ℝ → ℂ} (hg : MeasureTheory.Integrable g) :
    Continuous (FourierTransformInv.fourierInv g) := by
  have hc : Continuous (VectorFourier.fourierIntegral Real.fourierChar volume (-innerₗ ℝ) g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hg
  exact hc

/-- The trigonometric-polynomial factor `x ↦ Σ_{n ∈ T} F n · e^{2πi n x}` of the wide-bump
amplitude is `C²` (indeed entire). -/
private theorem contDiff_two_mstWideExt_trig (F : ℤ → ℂ) (T : Finset ℤ) :
    ContDiff ℝ 2
      (fun x : ℝ => ∑ n ∈ T, F n * Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (x : ℂ)))) := by
  apply ContDiff.sum
  intro n hn
  apply ContDiff.mul contDiff_const
  exact (Complex.contDiff_exp (𝕜 := ℝ) (n := 2)).comp (by
    have : (fun x : ℝ => 2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ) * (x : ℂ)))
        = (fun x : ℝ => (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * (x : ℂ)) := by
      funext x; ring
    rw [this]
    exact contDiff_const.mul Complex.ofRealCLM.contDiff)

/-- The wide-bump amplitude `mstWideExt` is `C²`: it is the product of the rescaled bump
`x ↦ η (c_s x)` (`C²` since `η` is and `c_s ≥ 1`) with a trigonometric polynomial. -/
private theorem contDiff_two_mstWideExt (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ)
    (F : ℤ → ℂ) (T : Finset ℤ) (hηc : ContDiff ℝ 2 η) :
    ContDiff ℝ 2 (mstWideExt P χ η s F T) := by
  unfold mstWideExt
  exact (hηc.comp (contDiff_const.mul contDiff_id)).mul (contDiff_two_mstWideExt_trig F T)

/-- The rescaled bump `x ↦ η (c_s x)` has compact support: `η` vanishes off `[-1/2, 1/2]` and
`c_s ≥ 1 > 0`, so the support is contained in the compact interval `[-1/(2 c_s), 1/(2 c_s)]`. -/
private theorem hasCompactSupport_rescaled_bump (P : Polynomial ℤ) (η : ℝ → ℂ) (s : ℕ)
    (hηsup : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    HasCompactSupport (fun x : ℝ => η (mstWideC P s * x)) := by
  have hc : 0 < mstWideC P s := lt_of_lt_of_le zero_lt_one (one_le_mstWideC P s)
  refine HasCompactSupport.intro
    (K := Set.Icc (-(1 / (2 * mstWideC P s))) (1 / (2 * mstWideC P s))) isCompact_Icc ?_
  intro x hx
  apply hηsup
  have hxabs : 1 / (2 * mstWideC P s) < |x| := by
    rw [lt_abs]
    by_contra h
    push Not at h
    exact hx (by rw [Set.mem_Icc]; exact ⟨by linarith [h.2], h.1⟩)
  rw [abs_mul, abs_of_nonneg hc.le]
  have hthis : mstWideC P s * (1 / (2 * mstWideC P s)) = 1 / 2 := by field_simp
  rw [← hthis]
  exact mul_lt_mul_of_pos_left hxabs hc

/-- The wide-bump amplitude `mstWideExt` has compact support (contained in the support of the
rescaled bump factor). -/
private theorem hasCompactSupport_mstWideExt (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ)
    (F : ℤ → ℂ) (T : Finset ℤ) (hηsup : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    HasCompactSupport (mstWideExt P χ η s F T) := by
  have hmul := hasCompactSupport_rescaled_bump P η s hηsup
  unfold mstWideExt
  exact hmul.mul_right

/-- The wide-bump amplitude `mstWideExt` is integrable (`C²` with compact support). -/
private theorem integrable_mstWideExt (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ)
    (F : ℤ → ℂ) (T : Finset ℤ) (hηc : ContDiff ℝ 2 η)
    (hηsup : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    MeasureTheory.Integrable (mstWideExt P χ η s F T) :=
  (contDiff_two_mstWideExt P χ η s F T hηc).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_mstWideExt P χ η s F T hηsup)

/-- **Continuity of the band-limited interpolant of the wide-bump multiplier.**
`mstWideLat = 𝓕⁻ (mstWideExt)` is the inverse Fourier transform of the `C²`, compactly supported
amplitude `mstWideExt`, hence of an integrable function, hence continuous. -/
theorem mstWideLat_continuous (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ) (F : ℤ → ℂ)
    (T : Finset ℤ) (hηc : ContDiff ℝ 2 η) (hηsup : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    Continuous (Work.Maximal.mstWideLat P χ η s F T) := by
  have h := continuous_fourierInv_of_integrable (integrable_mstWideExt P χ η s F T hηc hηsup)
  simpa only [mstWideLat] using h

end

end Work.Maximal
