import Mathlib
import Submission.Lib.Unif2.Work.Analysis.Complex.Hormander.weighted_dbar_local

/-!
# The weighted measure `e^{-φ} dλ` on `ℂ`, and the L² plumbing for the `∂̄`-existence theorem

This module collects the (elementary) measure-theoretic bookkeeping needed by
`Work.Analysis.Complex.Hormander.exists_dbar_solution_weighted`, the weighted Hörmander
`∂̄`-existence theorem of `NOTES_divisor_chapter_plan.md` §28:

* the weighted measure `wMeasure φ = volume.withDensity (ofReal ∘ exp ∘ neg ∘ φ)`;
* the translation of integrals against it into weighted integrals against Lebesgue measure
  (`integral_wMeasure`, `integral_wMeasure_real`);
* the identification `‖MemLp.toLp F hF‖ ^ 2 = ∫ z, ‖F z‖ ^ 2 ∂(wMeasure φ)`, which turns the
  *integral* form of the weighted Bochner--Kodaira estimate
  (`weighted_dbar_adjoint_estimate_tsupport`) into the *norm* inequality
  `‖v‖ ≤ (1 / √c) ‖P v‖` used by the Hahn--Banach/Riesz step.

Conventions: `dbar = ∂_x + i∂_y = 2∂_z̄`, `dbarBar = ∂_x - i∂_y = 2∂_z`.  Mathlib's inner product is
conjugate-linear in its *first* argument, so the weighted sesquilinear pairing used below is
`(a, b)_φ = ∫ conj a · b · e^{-φ}`, i.e. the `L²` inner product of `wMeasure φ`.
-/

open MeasureTheory
open scoped ENNReal Topology InnerProductSpace

noncomputable section

namespace Work.Analysis.Complex.Hormander

/-- The weighted measure `e^{-φ} dλ` on `ℂ`. -/
def wMeasure (φ : ℂ → ℝ) : Measure ℂ :=
  volume.withDensity (fun z => ENNReal.ofReal (Real.exp (-(φ z))))

theorem measurable_wMeasure_density {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    Measurable (fun z : ℂ => ENNReal.ofReal (Real.exp (-(φ z)))) :=
  (Real.continuous_exp.measurable.comp hφ.continuous.neg.measurable).ennreal_ofReal

theorem wMeasure_density_lt_top {φ : ℂ → ℝ} :
    ∀ᵐ z ∂(volume : Measure ℂ), ENNReal.ofReal (Real.exp (-(φ z))) < ∞ :=
  Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

/-- Integrals against `wMeasure φ` are weighted integrals against Lebesgue measure. -/
theorem integral_wMeasure {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℂ → E) :
    ∫ z, F z ∂(wMeasure φ) = ∫ z, Real.exp (-(φ z)) • F z := by
  rw [wMeasure, integral_withDensity_eq_integral_toReal_smul (measurable_wMeasure_density hφ)
    wMeasure_density_lt_top]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
    simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _)])

/-- Real-valued version of `integral_wMeasure`. -/
theorem integral_wMeasure_real {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (F : ℂ → ℝ) :
    ∫ z, F z ∂(wMeasure φ) = ∫ z, Real.exp (-(φ z)) * F z := by
  rw [integral_wMeasure hφ F]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only [smul_eq_mul])

/-- **The `L²` norm of a class is the weighted integral of `‖·‖²`.**  This is the bridge between
the *integral* form of the weighted Bochner--Kodaira estimate
(`weighted_dbar_adjoint_estimate_tsupport`) and the *abstract* norm inequality
`‖v‖ ≤ (1/√c) ‖P v‖` used in the Hahn--Banach/Riesz step of
`Work.Analysis.Complex.Hormander.exists_dbar_solution_weighted`. -/
theorem norm_toLp_sq {φ : ℂ → ℝ} {F : ℂ → ℂ} (hF : MemLp F 2 (wMeasure φ)) :
    ‖MemLp.toLp F hF‖ ^ 2 = ∫ z, (‖F z‖ ^ 2) ∂(wMeasure φ) := by
  have hint : Integrable (fun z => ‖F z‖ ^ 2) (wMeasure φ) :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have h2 : (∫ z, ((‖F z‖ ^ 2 : ℝ) : ℂ) ∂(wMeasure φ))
      = (((∫ z, (‖F z‖ ^ 2) ∂(wMeasure φ)) : ℝ) : ℂ) := by
    simpa only [Complex.ofRealCLM_apply] using
      (ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hint)
  have hinner : ⟪MemLp.toLp F hF, MemLp.toLp F hF⟫_ℂ
      = (((∫ z, (‖F z‖ ^ 2) ∂(wMeasure φ)) : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def, ← h2]
    refine integral_congr_ae ?_
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp hF] with z hz
    rw [hz, Complex.ofReal_pow]
    exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := F z)
  have hK : (((‖MemLp.toLp F hF‖ ^ 2) : ℝ) : ℂ)
      = ⟪MemLp.toLp F hF, MemLp.toLp F hF⟫_ℂ := by
    rw [Complex.ofReal_pow]
    exact (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := MemLp.toLp F hF)).symm
  exact Complex.ofReal_injective (hK.trans hinner)

/-- Integral form of `norm_toLp_sq` for an element of `L²`: the weighted integral of `‖·‖²` of a
representative is the square of the norm. -/
theorem integral_norm_sq_coeFn {φ : ℂ → ℝ} (z : MeasureTheory.Lp ℂ 2 (wMeasure φ)) :
    ∫ w, (‖(z : ℂ → ℂ) w‖ ^ 2) ∂(wMeasure φ) = ‖z‖ ^ 2 := by
  have h := norm_toLp_sq (φ := φ) (F := (z : ℂ → ℂ)) (Lp.memLp z)
  rw [MeasureTheory.Lp.toLp_coeFn] at h
  exact h.symm

end Work.Analysis.Complex.Hormander
