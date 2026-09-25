import Mathlib
import Submission.Work.BourgainPlan.Maximal.genWindow_analytic
import Submission.Work.BourgainPlan.Maximal.anisoAnnulusDefs
import Submission.Work.BourgainPlan.Maximal.polyProfile_fourier_dilation

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped ENNReal

/-! ## Invariance of `∫⁻ ‖𝓕⁻ ψ‖ₑ` under frequency dilation

The inverse Fourier transform on `ℝ` intertwines the frequency dilation `ψ ↦ ψ (c ·)` with the
spatial dilation `z ↦ z c⁻¹` up to the normalisation `c⁻¹`:

`𝓕⁻ (ψ (c ·)) (z) = c⁻¹ • 𝓕⁻ ψ (z c⁻¹)`   (`c > 0`).

Taking norms and changing variables `z ↦ c z` in the Lebesgue integral (`z = c w`,
`dz = c dw`) makes the two factors `c⁻¹` and `c` cancel, so the lintegral of the modulus of the
inverse Fourier transform is unchanged. Only the change-of-variables formula
`Measure.map (c • ·) volume = (𝔼 c)⁻¹ • volume` (itself a case of `map_addHaar_smul`) is needed,
which is why the result needs no integrability hypothesis on `ψ` at all. -/
theorem fourierInv_dilate_lintegral (ψ : ℝ → ℂ) (c : ℝ) (hc : 0 < c) : ∫⁻ z, ‖FourierTransform.fourierInv (fun ξ => ψ (c * ξ)) z‖ₑ = ∫⁻ z, ‖FourierTransform.fourierInv ψ z‖ₑ := by
  -- The pointwise dilation identity for the inverse Fourier transform.
  have hscale : ∀ z, FourierTransform.fourierInv (fun ξ => ψ (c * ξ)) z
      = c⁻¹ • FourierTransform.fourierInv ψ (z * c⁻¹) := by
    intro z
    rw [fourierInv_eq_polyE_integral, fourierInv_eq_polyE_integral]
    have hint := Measure.integral_comp_mul_left
      (fun u : ℝ => polyE (u * (z * c⁻¹)) * ψ u) c
    rw [abs_of_pos (inv_pos.mpr hc)] at hint
    rw [show (∫ x : ℝ, polyE ((c*x) * (z*c⁻¹)) * ψ (c*x)) = ∫ x : ℝ, polyE (x*z) * ψ (c*x) from by
        apply integral_congr_ae; filter_upwards with x
        rw [show (c*x)*(z*c⁻¹) = x*z from by field_simp]] at hint
    exact hint
  -- Norm of the dilation.
  have hnorm : ∀ z, ‖FourierTransform.fourierInv (fun ξ => ψ (c * ξ)) z‖ₑ
      = (ENNReal.ofReal c)⁻¹ * ‖FourierTransform.fourierInv ψ (z * c⁻¹)‖ₑ := by
    intro z
    rw [hscale z, enorm_smul, Real.enorm_eq_ofReal (by positivity : (0:ℝ) ≤ c⁻¹),
        ENNReal.ofReal_inv_of_pos hc]
  -- Scaling of Lebesgue measure under `z ↦ z c⁻¹` and under `w ↦ c w`.
  have hmap1 : Measure.map (fun z : ℝ => z * c⁻¹) (volume : Measure ℝ) = ENNReal.ofReal c • volume := by
    have h := Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) (r := c⁻¹) (by positivity : c⁻¹ ≠ 0)
    rw [Module.finrank_self, pow_one, inv_inv, abs_of_pos hc] at h
    simpa only [smul_eq_mul, mul_comm] using h
  have hmap2 : Measure.map (fun w : ℝ => c * w) (volume : Measure ℝ) = ENNReal.ofReal c⁻¹ • volume := by
    have h := Measure.map_addHaar_smul (μ := (volume : Measure ℝ)) (r := c) (by positivity : c ≠ 0)
    rw [Module.finrank_self, pow_one, abs_of_pos (inv_pos.mpr hc)] at h
    simpa only [smul_eq_mul] using h
  -- Change of variables for the lintegral of `‖𝓕⁻ ψ‖ₑ`.
  have hchange : ∫⁻ z, ‖FourierTransform.fourierInv ψ (z * c⁻¹)‖ₑ
      = ENNReal.ofReal c * ∫⁻ z, ‖FourierTransform.fourierInv ψ z‖ₑ := by
    apply le_antisymm
    · -- upper bound: substitute `z = c w`
      have h := lintegral_map_le (μ := (volume : Measure ℝ))
        (fun a : ℝ => ‖FourierTransform.fourierInv ψ (a * c⁻¹)‖ₑ) (g := fun w : ℝ => c * w)
        (measurable_const_mul c).aemeasurable
      rw [hmap2, lintegral_smul_measure] at h
      have hR : (∫⁻ a : ℝ, ‖FourierTransform.fourierInv ψ ((c*a) * c⁻¹)‖ₑ)
          = ∫⁻ w, ‖FourierTransform.fourierInv ψ w‖ₑ := by
        apply lintegral_congr; intro a
        rw [show (c*a)*c⁻¹ = a from by field_simp]
      rw [hR] at h
      have hmul : (ENNReal.ofReal c)⁻¹ * ∫⁻ z, ‖FourierTransform.fourierInv ψ (z * c⁻¹)‖ₑ
          ≤ ∫⁻ w, ‖FourierTransform.fourierInv ψ w‖ₑ := by
        simpa [smul_eq_mul, ENNReal.ofReal_inv_of_pos hc] using h
      calc ∫⁻ z, ‖FourierTransform.fourierInv ψ (z * c⁻¹)‖ₑ
          = (ENNReal.ofReal c * (ENNReal.ofReal c)⁻¹)
              * ∫⁻ z, ‖FourierTransform.fourierInv ψ (z * c⁻¹)‖ₑ := by
              rw [ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top,
                one_mul]
        _ = ENNReal.ofReal c * ((ENNReal.ofReal c)⁻¹
              * ∫⁻ z, ‖FourierTransform.fourierInv ψ (z * c⁻¹)‖ₑ) := by rw [mul_assoc]
        _ ≤ ENNReal.ofReal c * ∫⁻ w, ‖FourierTransform.fourierInv ψ w‖ₑ :=
              mul_le_mul_of_nonneg_left hmul (by positivity)
    · -- lower bound: substitute `w = z c⁻¹`
      have h := lintegral_map_le (μ := (volume : Measure ℝ))
        (fun w : ℝ => ‖FourierTransform.fourierInv ψ w‖ₑ) (g := fun z : ℝ => z * c⁻¹)
        (measurable_mul_const c⁻¹).aemeasurable
      rw [hmap1, lintegral_smul_measure] at h
      simpa [smul_eq_mul] using h
  -- Assemble: pull out the constant and apply the change of variables.
  calc ∫⁻ z, ‖FourierTransform.fourierInv (fun ξ => ψ (c * ξ)) z‖ₑ
      = ∫⁻ z, (ENNReal.ofReal c)⁻¹ * ‖FourierTransform.fourierInv ψ (z * c⁻¹)‖ₑ := lintegral_congr hnorm
    _ = (ENNReal.ofReal c)⁻¹ * ∫⁻ z, ‖FourierTransform.fourierInv ψ (z * c⁻¹)‖ₑ :=
          lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hc))
    _ = (ENNReal.ofReal c)⁻¹ * (ENNReal.ofReal c * ∫⁻ z, ‖FourierTransform.fourierInv ψ z‖ₑ) := by rw [hchange]
    _ = ∫⁻ z, ‖FourierTransform.fourierInv ψ z‖ₑ := by
          rw [← mul_assoc,
            ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top, one_mul]

end Work.BourgainPlan.Maximal
