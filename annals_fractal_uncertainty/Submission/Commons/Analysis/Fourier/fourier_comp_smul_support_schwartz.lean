import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Commons.Analysis.Fourier.fourier_scaled_translate

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

/-- The Fourier transform of a Schwartz function `φ` whose Fourier transform vanishes outside a
set `K`: the Fourier transform of the dilation `x ↦ φ (c • x)` (`c > 0`) vanishes at every
frequency `ξ` which is not of the form `c • a` with `a ∈ K`.

Indeed, by the scaling rule `𝓕 (x ↦ φ (c • x)) ξ = c ^ (-d) • 𝓕 φ (c⁻¹ • ξ)`, and
`c⁻¹ • ξ ∉ K` whenever `ξ ∉ c • K`, so `𝓕 φ (c⁻¹ • ξ) = 0`. -/
theorem fourier_comp_smul_support_schwartz {d : ℕ}
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) {c : ℝ} (hc : 0 < c)
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : ∀ ξ, ξ ∉ K → FourierTransform.fourier φ ξ = 0) :
    ∀ ξ, (∀ a ∈ K, ξ ≠ c • a) →
      FourierTransform.fourier
        (fun x : EuclideanSpace ℝ (Fin d) => (φ : EuclideanSpace ℝ (Fin d) → ℂ) (c • x)) ξ = 0 := by
  intro ξ hξ
  have hcne : c ≠ 0 := hc.ne'
  -- Scaling rule for the Fourier transform of the dilation by `c`.
  have hscale : FourierTransform.fourier
        (fun x : EuclideanSpace ℝ (Fin d) => (φ : EuclideanSpace ℝ (Fin d) → ℂ) (c • x)) ξ
      = ((c⁻¹) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin d))) •
        FourierTransform.fourier (φ : EuclideanSpace ℝ (Fin d) → ℂ) (c⁻¹ • ξ) := by
    have h := fourier_comp_inv_smul (V := EuclideanSpace ℝ (Fin d))
      (fun u : EuclideanSpace ℝ (Fin d) => (φ : EuclideanSpace ℝ (Fin d) → ℂ) u)
      (inv_pos.mpr hc) ξ
    rw [inv_inv] at h
    exact h
  have hnotmem : c⁻¹ • ξ ∉ K := by
    intro hmem
    exact hξ (c⁻¹ • ξ) hmem (smul_inv_smul₀ hcne ξ).symm
  rw [hscale, ← SchwartzMap.fourier_coe φ, hK (c⁻¹ • ξ) hnotmem, smul_zero]

end Commons.Analysis.Fourier