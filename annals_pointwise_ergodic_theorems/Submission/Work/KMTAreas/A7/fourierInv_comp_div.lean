import Mathlib

/-!
# Scaling of the inverse Fourier transform on `ℝ`

The main statement is the change-of-variables identity

`𝓕⁻ (fun θ => η (θ / c)) x = c • 𝓕⁻ η (c * x)`   (`c > 0`),

obtained from the Haar measure scaling `Measure.integral_comp_div`.  It is the
one-dimensional (rotation-free) special case of the scaling law for the Fourier
transform, kept here in the exact form requested by the `KMTAreas/A7` area.
-/

namespace Work.KMTAreas.A7

open MeasureTheory FourierTransform
open scoped FourierTransform

/-- Unfolding of the inverse Fourier transform on `ℝ` into an explicit integral
against the real Fourier character. -/
lemma fourierInv_eq_real (f : ℝ → ℂ) (w : ℝ) :
    FourierTransformInv.fourierInv f w = ∫ v : ℝ, Real.fourierChar (v * w) • f v := by
  rw [Real.fourierInv_eq]
  apply integral_congr_ae
  filter_upwards with v
  rw [Real.inner_apply]

theorem fourierInv_comp_div (η : ℝ → ℂ) {c : ℝ} (hc : 0 < c) :
    (fun x : ℝ => FourierTransformInv.fourierInv (fun θ : ℝ => η (θ / c)) x)
      = fun x : ℝ => (c : ℂ) • FourierTransformInv.fourierInv η (c * x) := by
  funext x
  rw [fourierInv_eq_real, fourierInv_eq_real]
  -- turn the `ℂ`-scalar multiplication into the real one, so that the Haar
  -- change of variables applies verbatim
  rw [Complex.coe_smul]
  have h := MeasureTheory.Measure.integral_comp_div
    (fun u : ℝ => Real.fourierChar (u * (c * x)) • η u) c
  rw [abs_of_pos hc] at h
  rw [← h]
  congr 1 with v
  rw [show v / c * (c * x) = v * x from by field_simp]

end Work.KMTAreas.A7
