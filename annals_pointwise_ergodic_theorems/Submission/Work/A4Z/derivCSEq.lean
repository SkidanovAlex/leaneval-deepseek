/-
# The derivative of the convolution `cS` acts on the first factor

`Work.KMTAreas.A4.cS u v` is the convolution of the two complex Schwartz functions `u`, `v` on `ℝ`
(`SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) u v`).  This file proves the elementary
calculus identity

  `(cS f g)' = cS f' g`,

i.e. differentiating the convolution commutes with convolving the derivative of the first factor.

The proof goes through the Fourier transform: by definition of `SchwartzMap.convolution`, `cS u v`
is the inverse Fourier transform of the pointwise product `mS (𝓕 u) (𝓕 v)`, and the classical rule
"differentiation = multiplication by `2πi ξ` on the Fourier side" is
`SchwartzMap.lineDerivOp_fourierInv_eq` / `SchwartzMap.fourier_lineDerivOp_eq`.  Since `𝓕` sends the
one-dimensional derivative `derivCLM ℂ ℂ` to multiplication by `2πi ξ` (the line derivative in
direction `1`), the identity reduces to the commutativity of `ℂ` in the identity

  `2πi ξ · (𝓕f ξ · 𝓕g ξ) = (2πi ξ · 𝓕f ξ) · 𝓕g ξ`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.offDecayDefs

namespace Work.A4Z

open scoped FourierTransform

open Work.KMTAreas.A4

/-- On `𝓢(ℝ, ℂ)`, `derivCLM ℂ ℂ` is the line derivative in direction `1`. -/
private lemma derivCLM_eq_lineDerivOp_one (h : SchwartzMap ℝ ℂ) :
    SchwartzMap.derivCLM ℂ ℂ h = LineDeriv.lineDerivOp (1 : ℝ) h := by
  ext x
  rw [SchwartzMap.derivCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    fderiv_apply_one_eq_deriv]

/-- The convolution `cS u v` is the inverse Fourier transform of the pointwise product
`mS (𝓕 u) (𝓕 v)`. -/
private lemma cS_eq_fourierInv (u v : SchwartzMap ℝ ℂ) :
    cS u v = 𝓕⁻ (mS (𝓕 u) (𝓕 v)) := by
  rw [← FourierPair.fourierInv_fourier_eq (E := SchwartzMap ℝ ℂ) (F := SchwartzMap ℝ ℂ) (cS u v),
    fourier_cS]

theorem derivCSEq (f g : SchwartzMap ℝ ℂ) :
    SchwartzMap.derivCLM ℂ ℂ (Work.KMTAreas.A4.cS f g)
      = Work.KMTAreas.A4.cS (SchwartzMap.derivCLM ℂ ℂ f) g := by
  rw [derivCLM_eq_lineDerivOp_one, cS_eq_fourierInv f g,
    cS_eq_fourierInv (SchwartzMap.derivCLM ℂ ℂ f) g,
    SchwartzMap.lineDerivOp_fourierInv_eq (mS (𝓕 f) (𝓕 g)) 1]
  -- the multiplier `ξ ↦ ξ` (times `2πi`) appearing in the Fourier picture of `derivCLM`
  have hχ : Function.HasTemperateGrowth (fun x : ℝ => inner ℝ x (1 : ℝ)) := by fun_prop
  -- the Fourier transform of `f'` is multiplication by `2πi ξ`
  have hF : 𝓕 (SchwartzMap.derivCLM ℂ ℂ f)
      = (2 * ↑Real.pi * Complex.I) •
        SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => inner ℝ x (1 : ℝ)) (𝓕 f) := by
    rw [derivCLM_eq_lineDerivOp_one]
    exact SchwartzMap.fourier_lineDerivOp_eq f 1
  rw [hF]
  -- it remains to identify the two multipliers of the inverse Fourier transform
  congr 1
  -- `mS` is linear in its first argument
  have h3 : mS ((2 * ↑Real.pi * Complex.I) •
        SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => inner ℝ x (1 : ℝ)) (𝓕 f)) (𝓕 g)
      = (2 * ↑Real.pi * Complex.I) •
        mS (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => inner ℝ x (1 : ℝ)) (𝓕 f)) (𝓕 g) := by
    show (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
        ((2 * ↑Real.pi * Complex.I) •
          SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => inner ℝ x (1 : ℝ)) (𝓕 f))) (𝓕 g) =
      (2 * ↑Real.pi * Complex.I) •
        (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ)
          (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => inner ℝ x (1 : ℝ)) (𝓕 f))) (𝓕 g)
    rw [map_smul, smul_apply]
  -- and pointwise multiplication by a scalar commutes with `mS`
  have h4 : mS (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => inner ℝ x (1 : ℝ)) (𝓕 f)) (𝓕 g)
      = SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => inner ℝ x (1 : ℝ))
          (mS (𝓕 f) (𝓕 g)) := by
    ext x
    simp only [mS_apply, SchwartzMap.smulLeftCLM_apply hχ, Complex.real_smul]
    ring
  rw [h3, h4]

end Work.A4Z
