import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.BoseBoxFock.FRK.windowDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.smearK_integrable`

`smearK r` is the inverse (`p`-convention) Fourier transform of the smooth, compactly supported
frequency cutoff `freqCut r = freqProfile (r⁻¹ • ·)`:

  `smearK r x = (2π)⁻³ ∫_p freqCut r p · cos ⟪p,x⟫ dp`.

Since `freqCut r` is `C^∞` with compact support (`r ≠ 0`), its inverse Fourier transform is a
Schwartz function; in particular it is integrable, which is the statement below.

The proof identifies `x ↦ (smearK r x : ℂ)` with `𝓕⁻ (smearProfile r)`, where the `C^∞_c` profile

  `smearProfile r ξ = ↑(freqProfile ((r⁻¹ · 2π) • ξ))`

is the cutoff rescaled by `2π` — the rescaling is the change of variables `p = 2π ξ` in the
`p`-convention integral.  Then `𝓕⁻` of a Schwartz function is a Schwartz function
(`SchwartzMap.fourierTransformCLM`), and Schwartz functions are integrable
(`SchwartzMap.integrable`).

The only analytic input is that the imaginary (sine) part of `∫ p, ↑(freqCut r p) · e^{i⟪p,x⟫}`
vanishes: the integrand `p ↦ freqCut r p · sin ⟪p,x⟫` is odd (`freqCut r` is radial/even), so its
integral is `0` (the oddness identity needs no integrability hypothesis: it is a statement about
the Bochner integral at the junk-value level, and both sides are handled by the neg-invariance of
Lebesgue measure).

## Main statements

* `Work.BoseBoxFock.FRK.smearProfile_hasCompactSupport`, `..._contDiff`;
* `Work.BoseBoxFock.FRK.sine_freqCut_integral_eq_zero`,
  `Work.BoseBoxFock.FRK.integral_freqCut_exp_eq_integral_cos` (the sine part drops);
* `Work.BoseBoxFock.FRK.fourierInv_smearProfile` (the change of variables `p = 2πξ`);
* `Work.BoseBoxFock.FRK.smearK_eq_fourierInv` (the identification of `smearK r` with `𝓕⁻`);
* `Work.BoseBoxFock.FRK.smearK_integrable` (the target).
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace Work.BoseBoxFock.FRK

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The rescaled cutoff profile -/

/-- The `C^∞` compactly supported profile whose inverse Fourier transform is `smearK r`:
`ξ ↦ ↑(freqProfile ((r⁻¹ · 2π) • ξ))` (the `2π`-rescaling of `freqCut r`). -/
noncomputable def smearProfile (r : ℝ) : E3 → ℂ :=
  fun ξ => ((freqProfile ((r⁻¹ * (2 * Real.pi)) • ξ) : ℝ) : ℂ)

lemma smearProfile_hasCompactSupport {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (smearProfile r) := by
  have hcs : HasCompactSupport (fun p : E3 => ((freqProfile p : ℝ) : ℂ)) :=
    freqProfile_hasCompactSupport.mono (by
      intro p hp
      simpa using hp)
  have hcomp := hcs.comp_homeomorph
    (Homeomorph.smulOfNeZero (r⁻¹ * (2 * Real.pi))
      (ne_of_gt (mul_pos (inv_pos.mpr hr) (by positivity))))
  exact hcomp

lemma smearProfile_contDiff (r : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (smearProfile r) := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : E3 => (r⁻¹ * (2 * Real.pi)) • ξ) := by fun_prop
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : E3 => freqProfile ((r⁻¹ * (2 * Real.pi)) • ξ)) :=
    freqProfile_contDiff.comp hφ
  exact Complex.ofRealCLM.contDiff.comp h1

/-! ## 2. The sine part of the Fourier integral vanishes -/

/-- The sine part of the `p`-integral vanishes: `p ↦ freqCut r p * sin ⟪p,x⟫` is odd. -/
lemma sine_freqCut_integral_eq_zero (r : ℝ) (x : E3) :
    ∫ p : E3, freqCut r p * Real.sin (inner ℝ p x) = 0 := by
  set f : E3 → ℝ := fun q => freqCut r q * Real.sin (inner ℝ q x) with hf
  have hodd : ∀ p : E3, f (-p) = -f p := by
    intro p
    simp only [hf]
    rw [freqCut_even r p, show inner ℝ (-p) x = -(inner ℝ p x) from by simp, Real.sin_neg]
    ring
  have key : (∫ p : E3, f p) = -(∫ p : E3, f p) := by
    calc (∫ p : E3, f p) = ∫ p : E3, f (-p) := (integral_neg_eq_self f volume).symm
      _ = ∫ p : E3, -f p := by
            apply integral_congr_ae
            filter_upwards with p
            exact hodd p
      _ = -(∫ p : E3, f p) := integral_neg f
  linarith

/-- The `p`-convention Fourier integral of the real cutoff against the complex exponential equals
the cosine integral: the `i sin` part drops by oddness. -/
lemma integral_freqCut_exp_eq_integral_cos {r : ℝ} (hr : 0 < r) (x : E3) :
    (∫ p : E3, (freqCut r p : ℂ) * Complex.exp (↑(inner ℝ p x) * Complex.I))
      = ((∫ p : E3, freqCut r p * Real.cos (inner ℝ p x) : ℝ) : ℂ) := by
  have hcs : HasCompactSupport (fun p : E3 => (freqCut r p : ℂ)) :=
    (freqCut_hasCompactSupport (ne_of_gt hr)).mono (by
      intro p hp
      simpa using hp)
  have hcont : Continuous (fun p : E3 => (freqCut r p : ℂ)) :=
    Complex.continuous_ofReal.comp (freqCut_contDiff (ne_of_gt hr)).continuous
  have hinner : Continuous (fun p : E3 => inner ℝ p x) := by fun_prop
  have hcosc : Continuous (fun p : E3 => ((Real.cos (inner ℝ p x) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_cos.comp hinner)
  have hsinc : Continuous (fun p : E3 => ((Real.sin (inner ℝ p x) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sin.comp hinner)
  have hint1 :
      Integrable (fun p : E3 => (freqCut r p : ℂ) * ((Real.cos (inner ℝ p x) : ℝ) : ℂ)) :=
    (hcont.mul hcosc).integrable_of_hasCompactSupport
      (hcs.mono (by intro p hp h; simp [h] at hp))
  have hint2 :
      Integrable (fun p : E3 => (freqCut r p : ℂ) * ((Real.sin (inner ℝ p x) : ℝ) : ℂ)
        * Complex.I) :=
    ((hcont.mul hsinc).mul continuous_const).integrable_of_hasCompactSupport
      (hcs.mono (by intro p hp h; simp [h] at hp))
  have hsplit : (∫ p : E3, (freqCut r p : ℂ) * Complex.exp (↑(inner ℝ p x) * Complex.I))
      = ∫ p : E3, ((freqCut r p : ℂ) * ((Real.cos (inner ℝ p x) : ℝ) : ℂ)
          + (freqCut r p : ℂ) * ((Real.sin (inner ℝ p x) : ℝ) : ℂ) * Complex.I) := by
    apply integral_congr_ae
    filter_upwards with p
    rw [Complex.exp_ofReal_mul_I, mul_add, mul_assoc]
  rw [hsplit, integral_add hint1 hint2, integral_mul_const]
  have hsin : (∫ p : E3, (freqCut r p : ℂ) * ((Real.sin (inner ℝ p x) : ℝ) : ℂ)) = 0 := by
    have h1 : (fun p : E3 => (freqCut r p : ℂ) * ((Real.sin (inner ℝ p x) : ℝ) : ℂ))
        = fun p : E3 => ((freqCut r p * Real.sin (inner ℝ p x) : ℝ) : ℂ) := by
      funext p; rw [Complex.ofReal_mul]
    rw [h1]
    rw [show (∫ (p : E3), ((freqCut r p * Real.sin (inner ℝ p x) : ℝ) : ℂ))
        = ((∫ p : E3, freqCut r p * Real.sin (inner ℝ p x) : ℝ) : ℂ) from integral_ofReal]
    rw [sine_freqCut_integral_eq_zero r x, Complex.ofReal_zero]
  rw [hsin, zero_mul, add_zero]
  have h1 : (fun p : E3 => (freqCut r p : ℂ) * ((Real.cos (inner ℝ p x) : ℝ) : ℂ))
      = fun p : E3 => ((freqCut r p * Real.cos (inner ℝ p x) : ℝ) : ℂ) := by
    funext p; rw [Complex.ofReal_mul]
  rw [h1]
  rw [show (∫ (p : E3), ((freqCut r p * Real.cos (inner ℝ p x) : ℝ) : ℂ))
      = ((∫ p : E3, freqCut r p * Real.cos (inner ℝ p x) : ℝ) : ℂ) from integral_ofReal]

/-! ## 3. The inverse Fourier transform of the rescaled cutoff -/

/-- Change of variables `p = 2π ξ` in the inverse Fourier transform of `smearProfile r`: the
`p`-convention form of `𝓕⁻ (smearProfile r)`. -/
lemma fourierInv_smearProfile (r : ℝ) (hr : 0 < r) (x : E3) :
    𝓕⁻ (smearProfile r) x
      = ((((2 * Real.pi) ^ 3 : ℝ)⁻¹ : ℂ)) * ∫ p : E3,
          Complex.exp (↑(inner ℝ p x) * Complex.I) *
            ((freqProfile (r⁻¹ • p) : ℝ) : ℂ) := by
  rw [Real.fourierInv_eq']
  simp only [smul_eq_mul, smearProfile]
  have hcomp : (fun v : E3 => Complex.exp (↑(2 * Real.pi * inner ℝ v x) * Complex.I) *
        ((freqProfile ((r⁻¹ * (2 * Real.pi)) • v) : ℝ) : ℂ))
      = (fun v : E3 => (fun p : E3 => Complex.exp (↑(inner ℝ p x) * Complex.I) *
          ((freqProfile (r⁻¹ • p) : ℝ) : ℂ)) ((2 * Real.pi) • v)) := by
    funext v
    simp only []
    have h1 : inner ℝ ((2 * Real.pi) • v) x = 2 * Real.pi * inner ℝ v x :=
      real_inner_smul_left _ _ _
    have h2 : (r⁻¹ * (2 * Real.pi)) • v = r⁻¹ • ((2 * Real.pi) • v) := (smul_smul _ _ _).symm
    rw [h1, h2]
  rw [hcomp, Measure.integral_comp_smul_of_nonneg (μ := volume) (hR := by positivity)
    (fun p : E3 => Complex.exp (↑(inner ℝ p x) * Complex.I) *
      ((freqProfile (r⁻¹ • p) : ℝ) : ℂ)) (2 * Real.pi),
    finrank_euclideanSpace, Fintype.card_fin, Complex.real_smul]
  rw [Complex.ofReal_inv]

/-! ## 4. The identification of `smearK` with an inverse Fourier transform -/

/-- The `p`-convention integral defining `smearK` is exactly
`(2π)⁻³ ∫_p ↑(freqCut r p) · cos ⟪p,x⟫`. -/
lemma smearK_eq_expIntegral (r : ℝ) (hr : 0 < r) (x : E3) :
    ((smearK r x : ℝ) : ℂ)
      = ((((2 * Real.pi) ^ 3 : ℝ)⁻¹ : ℂ)) *
        ((∫ p : E3, freqCut r p * Real.cos (inner ℝ p x) : ℝ) : ℂ) := by
  simp only [smearK]
  push_cast
  ring

/-- **The identification**: `(smearK r · : ℂ)` is the inverse Fourier transform of the `C^∞_c`
profile `smearProfile r`. -/
lemma smearK_eq_fourierInv_pointwise (r : ℝ) (hr : 0 < r) (x : E3) :
    ((smearK r x : ℝ) : ℂ) = 𝓕⁻ (smearProfile r) x := by
  rw [fourierInv_smearProfile r hr x, smearK_eq_expIntegral r hr x]
  congr 1
  rw [← integral_freqCut_exp_eq_integral_cos hr x]
  apply integral_congr_ae
  filter_upwards with p
  show (freqCut r p : ℂ) * Complex.exp (↑(inner ℝ p x) * Complex.I)
      = Complex.exp (↑(inner ℝ p x) * Complex.I) * ((freqProfile (r⁻¹ • p) : ℝ) : ℂ)
  rw [freqCut]
  exact mul_comm _ _

/-- Function-level form of `smearK_eq_fourierInv_pointwise`. -/
lemma smearK_eq_fourierInv (r : ℝ) (hr : 0 < r) :
    (fun x : E3 => ((smearK r x : ℝ) : ℂ)) = 𝓕⁻ (smearProfile r) := by
  funext x
  exact smearK_eq_fourierInv_pointwise r hr x

/-! ## 5. The target -/

theorem smearK_integrable {r : ℝ} (hr : 0 < r) :
    MeasureTheory.Integrable
      (fun x : EuclideanSpace ℝ (Fin 3) => ((Work.BoseBoxFock.FRK.smearK r x : ℝ) : ℂ)) := by
  let G : SchwartzMap E3 ℂ :=
    (smearProfile_hasCompactSupport hr).toSchwartzMap (smearProfile_contDiff r)
  have hint : Integrable (fun x : E3 => (𝓕⁻ G) x) volume := SchwartzMap.integrable (𝓕⁻ G)
  rw [smearK_eq_fourierInv r hr]
  refine hint.congr ?_
  filter_upwards with x
  rw [SchwartzMap.fourierInv_coe]
  rfl

end Work.BoseBoxFock.FRK
