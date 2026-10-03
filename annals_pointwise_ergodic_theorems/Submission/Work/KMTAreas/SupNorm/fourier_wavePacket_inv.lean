import Mathlib

/-!
# Scaling and modulation for the inverse Fourier transform on `ℝ`

The target `Work.KMTAreas.SupNorm.fourier_wavePacket_inv` is the inversion of the
wave-packet normalisation used in the `SupNorm` area: for a frequency bump `ψ`
concentrated at scale `δ > 0` and centred at the frequency `x₀`, the inverse Fourier
transform of the rescaled/translated bump is again the inverse Fourier transform of `ψ`,
evaluated at `δ * x` and modulated by the character `e(x₀ x)`:

`𝓕⁻ (fun ξ => ψ ((ξ - x₀) / δ)) x = δ * e(x₀ x) * 𝓕⁻ ψ (δ * x)`.

The proof unfolds the inverse Fourier transform into the explicit integral
`𝓕⁻ f w = ∫ v, e(v * w) • f v`, performs the affine change of variables
`v = x₀ + δ * u` (translation invariance of Lebesgue measure followed by the dilation
rule `∫ v, g (v / δ) = |δ| • ∫ g`), and then splits the character with its additivity:
`e((x₀ + δ u) * x) = e(x₀ x) * e(u * (δ x))`, pulling the constant `e(x₀ x)` out of the
integral.

## Layout

* `wavePacket_fourierInv_eq_integral` — the inverse Fourier transform as an integral
  against the real Fourier character `e = Real.fourierChar`;
* `wavePacket_integral_comp_sub_div` — the affine change of variables
  `∫ v, G ((v - a) / δ) = δ * ∫ u, G u` (from the translation invariance of Lebesgue
  measure and `Measure.integral_comp_div`);
* `fourier_wavePacket_inv` — the statement, assembled from the two.
-/

open MeasureTheory

namespace Work.KMTAreas.SupNorm

/-- The inverse Fourier transform on `ℝ`, written as an integral against the real Fourier
character `Real.fourierChar`. -/
lemma wavePacket_fourierInv_eq_integral (f : ℝ → ℂ) (w : ℝ) :
    FourierTransformInv.fourierInv f w = ∫ v : ℝ, Real.fourierChar (v * w) • f v := by
  rw [Real.fourierInv_eq]
  congr with v
  rw [Real.inner_apply]

/-- Affine change of variables for the Lebesgue integral on `ℝ`:
`∫ v, G ((v - a) / δ) = δ * ∫ u, G u` for `δ > 0`.  (The integral of `G` is the Bochner
integral, so the identity holds for every `G`, integrable or not.) -/
lemma wavePacket_integral_comp_sub_div (G : ℝ → ℂ) {δ : ℝ} (hδ : 0 < δ) (a : ℝ) :
    (∫ v : ℝ, G ((v - a) / δ)) = (δ : ℂ) * ∫ u : ℝ, G u := by
  have h1 : (∫ v : ℝ, G ((v - a) / δ)) = ∫ w : ℝ, G (w / δ) :=
    MeasureTheory.integral_sub_right_eq_self (fun w : ℝ => G (w / δ)) a
  rw [h1, MeasureTheory.Measure.integral_comp_div G δ, abs_of_pos hδ, Complex.real_smul]

theorem fourier_wavePacket_inv (ψ : ℝ → ℂ) {δ : ℝ} (hδ : 0 < δ) (x₀ x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ => ψ ((ξ - x₀) / δ)) x
      = (δ : ℂ) * (Real.fourierChar (x₀ * x) : ℂ) * FourierTransformInv.fourierInv ψ (δ * x) := by
  -- Step 1: the affine change of variables `v = x₀ + δ * u`.
  have hA : (∫ v : ℝ, Real.fourierChar (v * x) • ψ ((v - x₀) / δ))
      = (δ : ℂ) * ∫ u : ℝ, Real.fourierChar ((x₀ + δ * u) * x) • ψ u := by
    have h1 : (∫ v : ℝ, Real.fourierChar (v * x) • ψ ((v - x₀) / δ))
        = ∫ v : ℝ, (fun u : ℝ => Real.fourierChar ((x₀ + δ * u) * x) • ψ u) ((v - x₀) / δ) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with v
      have hv : x₀ + δ * ((v - x₀) / δ) = v := by field_simp; ring
      rw [hv]
    rw [h1,
      wavePacket_integral_comp_sub_div (fun u : ℝ => Real.fourierChar ((x₀ + δ * u) * x) • ψ u)
        hδ x₀]
  -- Step 2: split the character and pull the constant `e(x₀ x)` out of the integral.
  have hB : (∫ u : ℝ, Real.fourierChar ((x₀ + δ * u) * x) • ψ u)
      = (Real.fourierChar (x₀ * x) : ℂ) * ∫ u : ℝ, Real.fourierChar (u * (δ * x)) • ψ u := by
    rw [← MeasureTheory.integral_const_mul (Real.fourierChar (x₀ * x) : ℂ)
      (fun u : ℝ => Real.fourierChar (u * (δ * x)) • ψ u)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    rw [show (x₀ + δ * u) * x = x₀ * x + u * (δ * x) from by ring, AddChar.map_add_eq_mul,
      Circle.smul_def, Circle.coe_mul, smul_eq_mul, Circle.smul_def, smul_eq_mul]
    ring
  rw [wavePacket_fourierInv_eq_integral, wavePacket_fourierInv_eq_integral,
    hA, hB, ← wavePacket_fourierInv_eq_integral ψ (δ * x)]
  ring

end Work.KMTAreas.SupNorm
