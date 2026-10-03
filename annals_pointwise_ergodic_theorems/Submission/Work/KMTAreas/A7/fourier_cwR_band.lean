import Mathlib
import Submission.Work.KMTAreas.A7.Large.Defs

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory
open scoped FourierTransform

/-! ## The band of the coefficient function of a bump

The "coefficient function" of a bump `φ` with respect to the character `ee` is

  `s ↦ ∫ θ, φ θ * ee (-(s*θ))`,   `ee x = exp (2 π i x)`,

which interpolates the workspace's `cw φ j = ∫ θ, φ θ * ee (-(j*θ))` at the integers.  The two
lemmas below identify it with the Fourier transform of `φ` and record Fourier inversion in the
sign convention of this file; the target `fourier_cwR_band` is then immediate. -/

/-- **The coefficient function is the Fourier transform.**  For a Schwartz function `φ` and a real
`s`, `∫ θ, φ θ * ee (-(s*θ)) = 𝓕 φ s`. -/
theorem cwR_eq_fourier (φ : SchwartzMap ℝ ℂ) (s : ℝ) :
    (∫ θ, (φ : ℝ → ℂ) θ * ee (-(s * θ))) = 𝓕 (φ : ℝ → ℂ) s := by
  rw [Real.fourier_eq]
  have hpt : ∀ v : ℝ, 𝐞 (-inner ℝ v s) • (φ : ℝ → ℂ) v
      = (φ : ℝ → ℂ) v * ee (-(s * v)) := by
    intro v
    rw [Real.inner_apply, Circle.smul_def, smul_eq_mul, Real.fourierChar_apply, ee]
    have harg : (↑(2 * Real.pi * (-(v * s))) : ℂ) * Complex.I
        = (2 : ℂ) * ↑Real.pi * Complex.I * ↑(-(s * v)) := by
      push_cast
      ring
    rw [harg, mul_comm]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]

/-- **Fourier inversion for Schwartz functions** in the sign convention of this file:
`𝓕 (𝓕 φ) ξ = φ (-ξ)`. -/
theorem fourier_fourier_eq_neg (φ : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    𝓕 (𝓕 (φ : ℝ → ℂ)) ξ = (φ : ℝ → ℂ) (-ξ) := by
  have hFint : Integrable (𝓕 (φ : ℝ → ℂ)) := by
    change Integrable ((𝓕 φ : SchwartzMap ℝ ℂ) : ℝ → ℂ)
    exact (𝓕 φ).integrable
  have h1 : 𝓕⁻ (𝓕 (φ : ℝ → ℂ)) = (φ : ℝ → ℂ) :=
    Continuous.fourierInv_fourier_eq φ.continuous φ.integrable hFint
  have h2 := congrFun h1 (-ξ)
  rw [Real.fourierInv_eq_fourier_neg] at h2
  simpa using h2

/-
The band of the Fourier-coefficient function of a bump: if the Schwartz function `φ` is supported
in `[-β,β]`, then the real-variable "coefficient function"
`cwR φ s = ∫ θ, φ θ * ee (-(s*θ))` (which interpolates the workspace's `cw φ j = ∫ θ, φ θ * ee (-(j*θ))`
at the integers) has Fourier transform supported in `[-β,β]`.

Proof: `cwR φ` is (by `Real.fourierInv_eq`) the inverse Fourier transform of `φ`, hence its Fourier
transform is `𝓕(𝓕φ) = φ ∘ neg` (Fourier inversion for Schwartz functions); since `[-β,β]` is
symmetric, `supp (φ ∘ neg) ⊆ [-β,β]`, and `ξ ∉ Icc (-β) β` forces `φ (-ξ) = 0`.
-/
theorem fourier_cwR_band (β : ℝ) (hβ : 0 < β) (φ : SchwartzMap ℝ ℂ)
    (hφ : ∀ ξ : ℝ, (φ : ℝ → ℂ) ξ ≠ 0 → |ξ| ≤ β) :
    ∀ ξ : ℝ, ξ ∉ Set.Icc (-β) β →
      FourierTransform.fourier
        (fun s : ℝ => ∫ θ, (φ : ℝ → ℂ) θ * Work.KMTAreas.A7.ee (-(s * θ))) ξ = 0 := by
  intro ξ hξ
  -- the coefficient function is the Fourier transform of `φ`
  have hfun : (fun s : ℝ => ∫ θ, (φ : ℝ → ℂ) θ * ee (-(s * θ)))
      = (𝓕 (φ : ℝ → ℂ) : ℝ → ℂ) := funext (cwR_eq_fourier φ)
  rw [hfun, fourier_fourier_eq_neg φ ξ]
  -- `𝓕 (𝓕 φ) ξ = φ (-ξ)`, and `ξ ∉ [-β,β]` forces `φ (-ξ) = 0`
  by_contra h
  have hb := hφ (-ξ) h
  rw [abs_le] at hb
  exact hξ ⟨by linarith [hb.1], by linarith [hb.2]⟩

end

end Work.KMTAreas.A7
