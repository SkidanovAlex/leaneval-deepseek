import Mathlib
import Submission.Work.KMTAreas.MSW_defs

/-!
# Fourier transform of the Shannon interpolation operator

`mswInterp s u` is the Shannon interpolation of the finitely supported sequence `u`,
`∑_{m ∈ s} u m · K(· + m)` with `K = 𝓕⁻χ`.  Its Fourier transform is the product of the
cutoff `χ = 𝓕K` with the trigonometric polynomial `mswTrig s u` of the sequence:

  `𝓕 (mswInterp s u) = fun ξ ↦ χ ξ * mswTrig s u ξ`.

This is the frequency-space description of the de Leeuw transfer: the interpolated
function has Fourier support in `[-2,2]` (where `χ = 1`) and its Fourier coefficients are
the samples `u m`.

The proof is termwise: the Fourier transform converts the translation `x ↦ K (x + m)`
into multiplication by the character `ξ ↦ 𝐞 (m * ξ) = exp (2πi m ξ)`, and `𝓕K = χ`.
-/
open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.KMTAreas

/-- The Fourier transform converts a translation into multiplication by a character:
`𝓕 (fun x ↦ f (x + a)) = fun ξ ↦ 𝐞 (a * ξ) • 𝓕 f ξ`. -/
private lemma fourier_shift_add (f : ℝ → ℂ) (a : ℝ) :
    𝓕 (fun x => f (x + a)) = fun ξ => (𝐞 (a * ξ) : ℂ) • 𝓕 f ξ := by
  have h := VectorFourier.fourierIntegral_comp_add_right (𝕜 := ℝ) (V := ℝ) (W := ℝ) (E := ℂ)
      Real.fourierChar volume (innerₗ ℝ) f a
  have h2 : (𝓕 (fun x : ℝ => f (x + a)))
      = VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
          (fun x => f (x + a)) := rfl
  rw [h2]
  have h3 : (fun x : ℝ => f (x + a)) = (f ∘ fun v : ℝ => v + a) := rfl
  rw [h3, h]
  funext ξ
  rw [show (innerₗ ℝ a) ξ = a * ξ from by simp [innerₗ_apply_apply, mul_comm]]
  rfl

/-- The value of the Fourier character is the exponential appearing in `mswTrig`:
`𝐞 (m * ξ) = exp (2πi m ξ)` for integer `m`. -/
private lemma fourierChar_eq_exp (m : ℤ) (ξ : ℝ) :
    (𝐞 ((m : ℝ) * ξ) : ℂ)
      = Complex.exp (2 * ↑Real.pi * Complex.I * (m : ℂ) * (ξ : ℂ)) := by
  rw [Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-- Pointwise Fourier transform of a translate of a Schwartz function:
`𝓕 (f (· - a)) ξ = 𝐞 (a * ξ) * 𝓕 f ξ`. -/
private lemma fourier_compSubConstCLM_neg_apply (f : SchwartzMap ℝ ℂ) (m ξ : ℝ) :
    (𝓕 (f.compSubConstCLM ℝ (-m))) ξ = (𝐞 (m * ξ) : ℂ) * (𝓕 f) ξ := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  have hcoe : (⇑(f.compSubConstCLM ℝ (-m)) : ℝ → ℂ) = fun x => f (x + m) := by
    funext x
    rw [SchwartzMap.compSubConstCLM_apply]
    ring_nf
  rw [hcoe]
  have := congr_fun (fourier_shift_add (⇑f) m) ξ
  simpa [Circle.smul_def] using this

theorem MSW_fourier_interp (s : Finset ℤ) (u : ℤ → ℂ) :
    FourierTransform.fourier (mswInterp s u) = fun ξ => mswChi ξ * mswTrig s u ξ := by
  funext ξ
  rw [mswInterp, FourierTransform.fourier_sum]
  rw [sum_apply]
  have hterm : ∀ m ∈ s,
      (𝓕 (u m • (mswK.compSubConstCLM ℝ (-(m : ℝ))))) ξ
        = u m * (Complex.exp (2 * ↑Real.pi * Complex.I * (m : ℂ) * (ξ : ℂ)) * mswChi ξ) := by
    intro m _
    rw [FourierSMul.fourier_smul, smul_apply, smul_eq_mul]
    rw [fourier_compSubConstCLM_neg_apply]
    rw [mswChi_eq_fourier_mswK]
    rw [fourierChar_eq_exp]
  rw [Finset.sum_congr rfl hterm]
  rw [mswTrig, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

end Work.KMTAreas
