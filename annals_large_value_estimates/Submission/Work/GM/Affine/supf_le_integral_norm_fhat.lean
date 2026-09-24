import Mathlib
import Submission.Work.GM.Affine.setup

/-!
# `supf f ≤ ∫ ξ, ‖Fhat f ξ‖`

For the GM §9 test function `f` (continuous, compactly supported, non-negative) with an
integrable Fourier transform, the supremum of `f` is bounded by the `L¹` norm of its
Fourier transform.

This is immediate from Fourier inversion: for a point `x` where `f` attains its supremum,
`f x = ∫ ξ, e(ξ x) Fhat f ξ`, so by the triangle inequality for the Bochner integral

  `supf f = f x = ‖f x‖ ≤ ∫ ξ, ‖e(ξ x) Fhat f ξ‖ = ∫ ξ, ‖Fhat f ξ‖`.

The proof uses Mathlib's `Continuous.fourierInv_fourier_eq`, which needs exactly the
integrability of `f` (automatic here from continuity + compact support) and integrability of
`Fhat f` — the hypothesis `hint`.
-/

open Complex MeasureTheory
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

theorem supf_le_integral_norm_fhat {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) (hnn : ∀ u, 0 ≤ f u) (hint : MeasureTheory.Integrable (Fhat f)) : supf f ≤ ∫ ξ, ‖Fhat f ξ‖ := by
  -- `f` attains its supremum at some point `x`.
  obtain ⟨x, hx⟩ := exists_eq_supf hf hcs
  have hcont : Continuous (fun u : ℝ => (f u : ℂ)) := Complex.continuous_ofReal.comp hf
  have hg : Integrable (fun u : ℝ => (f u : ℂ)) :=
    (hf.integrable_of_hasCompactSupport hcs).ofReal
  have hFint : Integrable (𝓕 (fun u : ℝ => (f u : ℂ))) := hint
  -- Fourier inversion at `x`.
  have hinv := Continuous.fourierInv_fourier_eq hcont hg hFint
  have hxinv : (f x : ℂ) = ∫ ξ, (𝐞 (inner ℝ ξ x)) • Fhat f ξ := by
    have h1 : 𝓕⁻ (𝓕 (fun u : ℝ => (f u : ℂ))) x = (f x : ℂ) := congrFun hinv x
    rw [← h1, Real.fourierInv_eq]
    simp only [Fhat]
  calc supf f = f x := hx.symm
    _ = ‖(f x : ℂ)‖ := by
        rw [show ‖(f x : ℂ)‖ = |f x| from RCLike.norm_ofReal (f x), abs_of_nonneg (hnn x)]
    _ = ‖∫ ξ, (𝐞 (inner ℝ ξ x)) • Fhat f ξ‖ := by rw [hxinv]
    _ ≤ ∫ ξ, ‖(𝐞 (inner ℝ ξ x)) • Fhat f ξ‖ := norm_integral_le_integral_norm _
    _ = ∫ ξ, ‖Fhat f ξ‖ := by
        apply integral_congr_ae
        filter_upwards with ξ
        exact Circle.norm_smul (𝐞 (inner ℝ ξ x)) (Fhat f ξ)

end

end Work.GM.Affine
