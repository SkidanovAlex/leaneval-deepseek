import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseBoxFock.FRK.windowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.smearK_kinFT` — the smoothing kernel has symbol `freqCut r`

`smearK r x = (2π)⁻³∫_p freqCut r p · cos⟪p,x⟫ dp` is the inverse `p`-convention Fourier
transform of the compactly supported cutoff `freqCut r` (`windowDefs`).  This module proves that
the (forward) `p`-convention transform `Submission.BoseGases.kinFT` of that kernel is exactly the
cutoff again:

  `kinFT (smearK r ·) = freqCut r`  as functions into `ℂ`,

i.e. Fourier inversion for the pair (forward `kinFT`, inverse `smearK`).  Concretely
`smearK r` is `𝓕⁻` of the complexification of `v ↦ freqCut r (2π • v)`, and Mathlib's Fourier
inversion (`Continuous.fourier_fourierInv_eq`) inverts `𝓕⁻`.

## Contents

* `hasCompactSupport_complexification`, `hasCompactSupport_complexification_comp` — bookkeeping
  for the complexification of a compactly supported real function;
* `fourierInv_complexification_comp` — the pointwise evaluation of `𝓕⁻ (↑(F (2π • ·)))`, using
  that the integrand is a complexification of a real function (so its imaginary part is the
  integral of an odd function) and the Haar rescaling `p = 2π • v`;
* `smearK_kinFT` — the target.
-/

noncomputable section

open MeasureTheory Filter

namespace Work.BoseBoxFock.FRK

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The complexification of a compactly supported real function has compact support. -/
lemma hasCompactSupport_complexification {F : E3 → ℝ} (h : HasCompactSupport F) :
    HasCompactSupport (fun v : E3 => ((F v : ℝ) : ℂ)) := by
  refine h.mono ?_
  intro v hv
  rw [Function.mem_support] at hv ⊢
  intro h0
  exact hv (by rw [h0, Complex.ofReal_zero])

/-- The complexification of `v ↦ F (2π • v)` has compact support whenever `F` does. -/
lemma hasCompactSupport_complexification_comp {F : E3 → ℝ} (h : HasCompactSupport F) :
    HasCompactSupport (fun v : E3 => ((F ((2 * Real.pi) • v) : ℝ) : ℂ)) := by
  have h2 : (0:ℝ) < 2 * Real.pi := by positivity
  have h1 : HasCompactSupport (fun v : E3 => F ((2 * Real.pi) • v)) := by
    let φ : E3 ≃ₜ E3 := Homeomorph.smulOfNeZero (2 * Real.pi) (ne_of_gt h2)
    convert h.comp_homeomorph φ using 1
    ext v
    simp only [φ, Homeomorph.smulOfNeZero_apply, Function.comp_apply]
  exact hasCompactSupport_complexification h1

/-- **The inverse Fourier transform of a complexified rescaled real symbol.**  For a compactly
supported, smooth, even `F : E3 → ℝ`,

  `𝓕⁻ (↑(F (2π • ·))) x = (2π)⁻³ ∫_p F p · cos⟪p,x⟫ dp`.

The `cos` (rather than `e^{i⟪p,x⟫}`) arises because `F` is even: the imaginary part of the
integral is an integral of an odd function. -/
theorem fourierInv_complexification_comp {F : E3 → ℝ} (hcs : HasCompactSupport F)
    (hcd : ContDiff ℝ (⊤ : ℕ∞) F) (heven : ∀ z, F (-z) = F z) (x : E3) :
    FourierTransform.fourierInv (fun v : E3 => ((F ((2 * Real.pi) • v) : ℝ) : ℂ)) x
      = ((((2 * Real.pi) ^ 3 : ℝ)⁻¹ * ∫ p : E3, F p * Real.cos (inner ℝ p x) : ℝ) : ℂ) := by
  have h2π : (0:ℝ) < 2 * Real.pi := by positivity
  have hfin : Module.finrank ℝ E3 = 3 := by simp
  set ψ : E3 → ℂ := fun v => ((F ((2 * Real.pi) • v) : ℝ) : ℂ) with hψdef
  have hcdψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    rw [hψdef]
    exact Complex.ofRealCLM.contDiff.comp (hcd.comp (contDiff_const_smul (2 * Real.pi)))
  have hcsψ : HasCompactSupport ψ := by
    rw [hψdef]
    exact hasCompactSupport_complexification_comp hcs
  have hψcont : Continuous ψ := hcdψ.continuous
  have hintψ : Integrable ψ := hψcont.integrable_of_hasCompactSupport hcsψ
  -- the phase integrand is smooth with compact support, hence integrable
  have hint : Integrable (fun v : E3 =>
      Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) * ψ v) := by
    have hc : Continuous (fun v : E3 =>
        Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I)) := by fun_prop
    exact (hc.mul hψcont).integrable_of_hasCompactSupport hcsψ.mul_left
  -- the real part of the inverse transform
  have hre : (FourierTransform.fourierInv ψ x).re
      = ((2 * Real.pi) ^ 3 : ℝ)⁻¹ * ∫ p : E3, F p * Real.cos (inner ℝ p x) := by
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]
    have hcomm := ContinuousLinearMap.integral_comp_comm (L := Complex.reCLM)
      (φ := fun v : E3 => Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) * ψ v) hint
    simp only [Complex.reCLM_apply] at hcomm
    rw [← hcomm]
    calc ∫ v : E3, (Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) * ψ v).re
        = ∫ v : E3, F ((2 * Real.pi) • v) * Real.cos (2 * Real.pi * inner ℝ v x) := by
          refine integral_congr_ae ?_
          filter_upwards with v
          rw [hψdef, Complex.mul_re, Complex.exp_ofReal_mul_I]
          simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one]
          ring
      _ = ∫ v : E3, (fun p : E3 => F p * Real.cos (inner ℝ p x)) ((2 * Real.pi) • v) := by
          refine integral_congr_ae ?_
          filter_upwards with v
          simp only [real_inner_smul_left]
      _ = ((2 * Real.pi) ^ 3 : ℝ)⁻¹ * ∫ p : E3, F p * Real.cos (inner ℝ p x) := by
          rw [Measure.integral_comp_smul_of_nonneg (μ := (volume : Measure E3))
            (f := fun p : E3 => F p * Real.cos (inner ℝ p x)) (R := 2 * Real.pi)
            (hR := le_of_lt h2π), hfin, smul_eq_mul]
  -- the imaginary part of the inverse transform vanishes: the integrand is odd
  have him : (FourierTransform.fourierInv ψ x).im = 0 := by
    rw [Real.fourierInv_eq']
    simp only [smul_eq_mul]
    have hcomm := ContinuousLinearMap.integral_comp_comm (L := Complex.imCLM)
      (φ := fun v : E3 => Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) * ψ v) hint
    simp only [Complex.imCLM_apply] at hcomm
    rw [← hcomm]
    have hpt : ∀ v : E3, (Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) * ψ v).im
        = F ((2 * Real.pi) • v) * Real.sin (2 * Real.pi * inner ℝ v x) := by
      intro v
      rw [hψdef, Complex.mul_im, Complex.exp_ofReal_mul_I]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one]
      ring
    have hzero : ∫ v : E3, F ((2 * Real.pi) • v) * Real.sin (2 * Real.pi * inner ℝ v x) = 0 := by
      set k : E3 → ℝ := fun v => F ((2 * Real.pi) • v) * Real.sin (2 * Real.pi * inner ℝ v x)
        with hk
      have hodd : ∀ v : E3, k (-v) = -k v := by
        intro v
        simp only [hk]
        rw [smul_neg, heven, inner_neg_left, mul_neg, Real.sin_neg]
        ring
      have h1 : ∫ v : E3, k v = ∫ v : E3, k (-v) := (integral_neg_eq_self k volume).symm
      have h2 : (∫ v : E3, k (-v)) = ∫ v : E3, -k v :=
        integral_congr_ae (Filter.Eventually.of_forall hodd)
      have h3 : (∫ v : E3, -k v) = -∫ v : E3, k v := integral_neg k
      linarith
    calc ∫ v : E3, (Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) * ψ v).im
        = ∫ v : E3, F ((2 * Real.pi) • v) * Real.sin (2 * Real.pi * inner ℝ v x) :=
          integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = 0 := hzero
  refine Complex.ext ?_ ?_
  · rw [Complex.ofReal_re]; exact hre
  · rw [Complex.ofReal_im]; exact him

theorem smearK_kinFT {r : ℝ} (hr : 0 < r) :
    Submission.BoseGases.kinFT
        (fun x : EuclideanSpace ℝ (Fin 3) => ((Work.BoseBoxFock.FRK.smearK r x : ℝ) : ℂ))
      = fun p : EuclideanSpace ℝ (Fin 3) => ((Work.BoseBoxFock.FRK.freqCut r p : ℝ) : ℂ) := by
  have hrne : r ≠ 0 := ne_of_gt hr
  have h2πne : (2 * Real.pi) ≠ 0 := by positivity
  have hcsF : HasCompactSupport (freqCut r) := freqCut_hasCompactSupport hrne
  have hcdF : ContDiff ℝ (⊤ : ℕ∞) (freqCut r) := freqCut_contDiff hrne
  have hevenF : ∀ z : E3, freqCut r (-z) = freqCut r z := fun z => freqCut_even r z
  funext p
  set ψ : E3 → ℂ := fun v => ((freqCut r ((2 * Real.pi) • v) : ℝ) : ℂ) with hψdef
  -- `smearK r` is the inverse Fourier transform of the rescaled cutoff
  have hψ : (fun x : E3 => ((smearK r x : ℝ) : ℂ)) = FourierTransform.fourierInv ψ := by
    funext x
    rw [fourierInv_complexification_comp hcsF hcdF hevenF x]
    simp only [smearK]
  -- `ψ` is smooth with compact support, so `𝓕 ψ` is integrable (it is Schwartz)
  have hcdψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    rw [hψdef]
    exact Complex.ofRealCLM.contDiff.comp (hcdF.comp (contDiff_const_smul (2 * Real.pi)))
  have hcsψ : HasCompactSupport ψ := by
    rw [hψdef]
    exact hasCompactSupport_complexification_comp hcsF
  have hcontψ : Continuous ψ := hcdψ.continuous
  have hintψ : Integrable ψ := hcontψ.integrable_of_hasCompactSupport hcsψ
  have hintfψ : Integrable (FourierTransform.fourier ψ) := by
    have h1 : Integrable (⇑(FourierTransform.fourier (hcsψ.toSchwartzMap hcdψ))) :=
      SchwartzMap.integrable _
    rw [SchwartzMap.fourier_coe] at h1
    have h2 : (⇑(hcsψ.toSchwartzMap hcdψ) : E3 → ℂ) = ψ := by
      funext a
      exact HasCompactSupport.toSchwartzMap_toFun hcsψ hcdψ a
    rwa [h2] at h1
  have hinv : FourierTransform.fourier (FourierTransform.fourierInv ψ) = ψ :=
    Continuous.fourier_fourierInv_eq hcontψ hintψ hintfψ
  calc Submission.BoseGases.kinFT (fun x : E3 => ((smearK r x : ℝ) : ℂ)) p
      = FourierTransform.fourier (fun x : E3 => ((smearK r x : ℝ) : ℂ))
          ((2 * Real.pi)⁻¹ • p) := Work.SmallBoxBridge.Resolve.kinFT_eq_fourier _ _
    _ = FourierTransform.fourier (FourierTransform.fourierInv ψ) ((2 * Real.pi)⁻¹ • p) := by
          rw [hψ]
    _ = ψ ((2 * Real.pi)⁻¹ • p) := by rw [hinv]
    _ = ((freqCut r p : ℝ) : ℂ) := by
          simp only [hψdef, smul_smul, mul_inv_cancel₀ h2πne, one_smul]

end Work.BoseBoxFock.FRK
