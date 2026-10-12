import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Analysis.Fourier.coulomb_energy_fourier_lintegral_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Commons.Analysis.Fourier

/-- The lintegral of `g (c⁻¹ • x)` against an additive Haar measure `μ` equals
`c ^ finrank ℝ E` times the lintegral of `g`, for `c > 0`. -/
lemma lintegral_comp_inv_smul_of_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (g : E → ℝ≥0∞) {c : ℝ} (hc : 0 < c) :
    ∫⁻ q, g (c⁻¹ • q) ∂μ = ENNReal.ofReal (c ^ Module.finrank ℝ E) * ∫⁻ p, g p ∂μ := by
  have hcne : c ≠ 0 := ne_of_gt hc
  let e : E ≃ᵐ E := (Homeomorph.smul (Units.mk0 c⁻¹ (inv_ne_zero hcne))).toMeasurableEquiv
  have he : (e : E → E) = fun q => c⁻¹ • q := rfl
  have hstep : ∫⁻ q, g (e q) ∂μ = ∫⁻ p, g p ∂Measure.map e μ :=
    (MeasureTheory.lintegral_map_equiv (μ := μ) g e).symm
  have hstep' : ∫⁻ q, g (c⁻¹ • q) ∂μ = ∫⁻ p, g p ∂Measure.map (fun q : E => c⁻¹ • q) μ := by
    simpa [he] using hstep
  rw [hstep', Measure.map_addHaar_smul μ (inv_ne_zero hcne),
    MeasureTheory.lintegral_smul_measure]
  congr 1
  rw [inv_pow, inv_inv, abs_of_nonneg (pow_nonneg hc.le _)]

theorem lintegral_fourier_inv_smul_sq_div_le {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : MeasureTheory.Integrable f) (hf0 : 0 ≤ f) :
    ENNReal.ofReal (((2 * Real.pi) ^ 3)⁻¹) * (∫⁻ q, ENNReal.ofReal
        (‖(FourierTransform.fourier (fun x => (f x : ℂ)) : EuclideanSpace ℝ (Fin 3) → ℂ)
            ((2 * Real.pi)⁻¹ • q)‖ ^ 2 / ‖q‖ ^ 2))
      ≤ ENNReal.ofReal (1 / (4 * Real.pi)) *
          (∫⁻ x, ∫⁻ y, ENNReal.ofReal (f x * f y / ‖x - y‖)) := by
  set c : ℝ := 2 * Real.pi with hcdef
  have hc : 0 < c := by rw [hcdef]; positivity
  have hcne : c ≠ 0 := ne_of_gt hc
  set F : EuclideanSpace ℝ (Fin 3) → ℂ := fun x => (f x : ℂ) with hFdef
  set Fh : EuclideanSpace ℝ (Fin 3) → ℂ := FourierTransform.fourier F with hFhdef
  set Y : ℝ≥0∞ := ∫⁻ x, ∫⁻ y, ENNReal.ofReal (f x * f y / ‖x - y‖) with hYdef
  set Z : ℝ≥0∞ := ∫⁻ p, ENNReal.ofReal (‖Fh p‖ ^ 2 / ‖p‖ ^ 2) with hZdef
  have hmain : Z ≤ ENNReal.ofReal Real.pi * Y := by
    rw [hZdef, hYdef, hFhdef, hFdef]
    exact coulomb_energy_fourier_lintegral_le hf hf0
  -- pointwise identity, almost everywhere
  have hne : ∀ᵐ q : EuclideanSpace ℝ (Fin 3), q ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    rw [show {q : EuclideanSpace ℝ (Fin 3) | ¬ q ≠ 0} = {0} by ext q; simp]
    exact measure_singleton 0
  have hpt : ∀ᵐ q : EuclideanSpace ℝ (Fin 3),
      ENNReal.ofReal (‖Fh (c⁻¹ • q)‖ ^ 2 / ‖q‖ ^ 2)
        = ENNReal.ofReal ((c⁻¹) ^ 2) *
            ENNReal.ofReal (‖Fh (c⁻¹ • q)‖ ^ 2 / ‖c⁻¹ • q‖ ^ 2) := by
    filter_upwards [hne] with q hq
    have hb : ‖q‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hq)
    have hnorm : ‖c⁻¹ • q‖ ^ 2 = (c⁻¹) ^ 2 * ‖q‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hc.le)]
      ring
    rw [hnorm, ← ENNReal.ofReal_mul (sq_nonneg (c⁻¹))]
    congr 1
    field_simp
  have hX : (∫⁻ q, ENNReal.ofReal (‖Fh (c⁻¹ • q)‖ ^ 2 / ‖q‖ ^ 2))
      = ENNReal.ofReal ((c⁻¹) ^ 2) * (ENNReal.ofReal (c ^ 3) * Z) := by
    rw [lintegral_congr_ae hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    have hsc := lintegral_comp_inv_smul_of_pos (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (fun p : EuclideanSpace ℝ (Fin 3) => ENNReal.ofReal (‖Fh p‖ ^ 2 / ‖p‖ ^ 2)) hc
    simp only [finrank_euclideanSpace, Fintype.card_fin] at hsc
    rw [hsc, ← hZdef]
  have hconst : ENNReal.ofReal ((c ^ 3)⁻¹) * (ENNReal.ofReal ((c⁻¹) ^ 2) *
      ENNReal.ofReal (c ^ 3)) = ENNReal.ofReal (1 / (4 * Real.pi ^ 2)) := by
    have h1 : ENNReal.ofReal ((c⁻¹) ^ 2) * ENNReal.ofReal (c ^ 3)
        = ENNReal.ofReal ((c⁻¹) ^ 2 * c ^ 3) :=
      (ENNReal.ofReal_mul (sq_nonneg (c⁻¹))).symm
    rw [h1]
    have h2 : ENNReal.ofReal ((c ^ 3)⁻¹) * ENNReal.ofReal ((c⁻¹) ^ 2 * c ^ 3)
        = ENNReal.ofReal ((c ^ 3)⁻¹ * ((c⁻¹) ^ 2 * c ^ 3)) :=
      (ENNReal.ofReal_mul (by positivity)).symm
    rw [h2]
    congr 1
    rw [hcdef]
    field_simp
    ring
  have hconst2 : 1 / (4 * Real.pi ^ 2) * Real.pi = 1 / (4 * Real.pi) := by
    field_simp
  calc ENNReal.ofReal ((c ^ 3)⁻¹) * (∫⁻ q, ENNReal.ofReal (‖Fh (c⁻¹ • q)‖ ^ 2 / ‖q‖ ^ 2))
      = (ENNReal.ofReal ((c ^ 3)⁻¹) * (ENNReal.ofReal ((c⁻¹) ^ 2) *
          ENNReal.ofReal (c ^ 3))) * Z := by
        rw [hX]; ring
    _ = ENNReal.ofReal (1 / (4 * Real.pi ^ 2)) * Z := by rw [hconst]
    _ ≤ ENNReal.ofReal (1 / (4 * Real.pi ^ 2)) * (ENNReal.ofReal Real.pi * Y) :=
        mul_le_mul_right hmain _
    _ = ENNReal.ofReal (1 / (4 * Real.pi)) * Y := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1 / (4 * Real.pi ^ 2)),
          hconst2]

end Commons.Analysis.Fourier
