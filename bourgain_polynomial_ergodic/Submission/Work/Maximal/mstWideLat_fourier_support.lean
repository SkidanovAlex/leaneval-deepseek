import Mathlib
import Submission.Work.Maximal.mstWideLat_defs
import Submission.Work.BourgainPlan.Maximal.mstHat_decay_of_contDiff
import Submission.Work.Analysis.Fourier.fourier_fourierInv_band_limited
import Submission.Work.BourgainPlan.Maximal.integrable_fourierInv_of_contDiff_two_hasCompactSupport

/-!
# Band-limitedness of the wide-model interpolant `mstWideLat` (MST Theorem 1, Half 2)

The lattice-sampling step of the large-scale half of the level-`s` estimate
(`Work.Maximal.mstWideModel_lr_maximal`) needs the band-limited interpolant
`mstWideLat P χ η s F T = 𝓕⁻ (mstWideExt P χ η s F T)` to be **band-limited to the ball of radius
`1 / (2 c_s)`**, `c_s = mstWideC P s`: its Fourier transform must vanish outside
`[-1/(2 c_s), 1/(2 c_s)]`.

This is exactly the statement that the amplitude `mstWideExt x = η (c_s x) · Σ_{n ∈ T} F n e^{2πinx}`
is supported in the band `|x| ≤ 1/(2 c_s)`, together with Fourier inversion: since the amplitude
`g = mstWideExt` is `C²` with compact support, both `g` and `𝓕 g` are integrable, so
`𝓕 (𝓕⁻ g) = g` pointwise, and `g` vanishes off the band because `η` does.
-/

open MeasureTheory Finset
open scoped FourierTransform BigOperators

set_option autoImplicit false

namespace Work.Maximal

noncomputable section

/-- **A `C²` compactly supported function on `ℝ` has an integrable Fourier transform.**  This is
`Work.BourgainPlan.Maximal.integrable_fourierInv_of_contDiff_two_hasCompactSupport` read through the
identity `𝓕 φ = fun t => 𝓕⁻ φ (−t)` and the invariance of integrability under `x ↦ −x`. -/
private lemma integrable_fourier_of_contDiff_two_hasCompactSupport {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    MeasureTheory.Integrable (𝓕 φ) := by
  have h := Work.BourgainPlan.Maximal.integrable_fourierInv_of_contDiff_two_hasCompactSupport hφ hc
  have h2 : Integrable (fun t : ℝ => 𝓕⁻ φ (-t)) := h.comp_neg
  convert h2 using 1
  funext t
  simp [Real.fourierInv_eq_fourier_neg]

/-- **The wide-model interpolant is band-limited to `[-1/(2 c_s), 1/(2 c_s)]`.**  For any `ξ` with
`1/(2 c_s) < |ξ|`, the Fourier transform of `mstWideLat P χ η s F T` vanishes at `ξ`. -/
theorem mstWideLat_fourier_support (P : Polynomial ℤ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ) (F : ℤ → ℂ)
    (T : Finset ℤ) (hηc : ContDiff ℝ 2 η) (hηsup : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    ∀ ξ : ℝ, 1 / (2 * Work.Maximal.mstWideC P s) < |ξ| →
      FourierTransform.fourier (Work.Maximal.mstWideLat P χ η s F T) ξ = 0 := by
  intro ξ hξ
  -- `c_s ≥ 1`, hence the half-width `1/(2 c_s)` is positive.
  have hcpos : 0 < mstWideC P s := lt_of_lt_of_le zero_lt_one (one_le_mstWideC P s)
  -- the trigonometric factor of the amplitude, and the amplitude itself
  set Φ : ℝ → ℂ := fun x => ∑ n ∈ T, F n * Complex.exp (2 * Real.pi * Complex.I * ((n : ℂ) * (x : ℂ)))
    with hΦ
  set g : ℝ → ℂ := fun x => η (mstWideC P s * x) * Φ x with hg
  -- `g` vanishes off the band
  have hgvan : ∀ x : ℝ,
      x ∉ Set.Icc (-(1 / (2 * mstWideC P s))) (1 / (2 * mstWideC P s)) → g x = 0 := by
    intro x hx
    have hxr : 1 / (2 * mstWideC P s) < |x| := by
      by_contra h
      push Not at h
      exact hx (Set.mem_Icc.mpr (abs_le.mp h))
    have hbig : 1 / 2 < |mstWideC P s * x| := by
      have hr : mstWideC P s * (1 / (2 * mstWideC P s)) = 1 / 2 := by field_simp
      rw [abs_mul, abs_of_pos hcpos, ← hr]
      exact mul_lt_mul_of_pos_left hxr hcpos
    rw [hg]
    simp only
    rw [hηsup _ hbig, zero_mul]
  -- `g` is `C²` ...
  have hgcd : ContDiff ℝ 2 g := by
    have hsum : ContDiff ℝ 2 Φ := by
      rw [hΦ]
      apply ContDiff.sum
      intro n _
      have hlin : ContDiff ℝ 2 (fun x : ℝ => 2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)) :=
        contDiff_const.mul Complex.ofRealCLM.contDiff
      have hlin' : ContDiff ℝ 2 (fun x : ℝ => 2 * Real.pi * Complex.I * ((n : ℂ) * (x : ℂ))) := by
        convert hlin using 1
        funext x
        ring
      exact contDiff_const.mul (Complex.contDiff_exp.comp hlin')
    have hW : ContDiff ℝ 2 (fun x : ℝ => η (mstWideC P s * x)) :=
      hηc.comp (contDiff_const.mul contDiff_id)
    rw [hg]
    exact hW.mul hsum
  -- ... and compactly supported,
  have hgcs : HasCompactSupport g := by
    exact HasCompactSupport.intro
      (K := Set.Icc (-(1 / (2 * mstWideC P s))) (1 / (2 * mstWideC P s))) isCompact_Icc
      (fun x hx => hgvan x hx)
  have hgcont : Continuous g := hgcd.continuous
  have hgint : Integrable g := hgcont.integrable_of_hasCompactSupport hgcs
  have hgftint : Integrable (𝓕 g) :=
    integrable_fourier_of_contDiff_two_hasCompactSupport hgcd hgcs
  -- so Fourier inversion applies at `ξ`
  have key : 𝓕 (𝓕⁻ g) ξ = g ξ := hgint.fourier_fourierInv_eq hgftint hgcont.continuousAt
  have hξnot : ξ ∉ Set.Icc (-(1 / (2 * mstWideC P s))) (1 / (2 * mstWideC P s)) := by
    intro hmem
    have hle : |ξ| ≤ 1 / (2 * mstWideC P s) := abs_le.mpr (Set.mem_Icc.mp hmem)
    linarith [hξ]
  calc FourierTransform.fourier (mstWideLat P χ η s F T) ξ = 𝓕 (𝓕⁻ g) ξ := rfl
    _ = g ξ := key
    _ = 0 := hgvan ξ hξnot

end

end Work.Maximal
