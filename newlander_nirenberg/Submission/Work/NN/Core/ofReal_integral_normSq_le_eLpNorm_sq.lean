import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Polydisc

/-!
# From a pointwise bound `‖G‖ ≤ M·‖h‖` to an `L²`-bound for `G`

This file proves `Work.NN.Core.ofReal_integral_normSq_le_eLpNorm_sq`: for a `C¹` function `G`
on `ℂⁿ = Fin n → ℂ` with compact support inside the polydisc `polydisc 0 ρ`, dominated
pointwise by `M·‖h‖` with `M ≥ 0`,

  `∫ ‖G‖² ≤ M² · (eLpNorm h 2 (volume.restrict (polydisc 0 ρ)))²`.

The proof reduces the Bochner integral `∫ ‖G‖²` to the Lebesgue integral `∫⁻ ‖G‖ₑ²` (using
integrability of `‖G‖²`, which follows from continuity and compact support), transfers the
integral from the whole space to the polydisc (using that `G` vanishes off its support), and then
applies monotonicity of the Lebesgue integral to the pointwise bound, together with the identity
`(eLpNorm h 2 μ)² = ∫⁻ ‖h‖ₑ² ∂μ` (for a.e. strongly measurable `h`).
-/

noncomputable section

open scoped ENNReal
open MeasureTheory

namespace Work.NN.Core

/-- The `ℝ≥0∞`-valued `2`-nd power of the extended norm of a complex number, written as an
`ENNReal.ofReal`. -/
private lemma enorm_sq_eq_ofReal' (x : ℂ) : ‖x‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [enorm_eq_nnnorm]
  rw [show (↑‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from (ENNReal.ofReal_coe_nnreal (p := ‖x‖₊)).symm]
  rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]

/-- **Core `L²`-inequality.**  For a measure `μ`, an integrable function `F` (in the sense that
`z ↦ ‖F z‖²` is integrable) and a pointwise domination `‖F z‖ ≤ M ‖H z‖` with `M ≥ 0`,

  `ofReal (∫ ‖F‖²) ≤ ofReal (M²) * (eLpNorm H 2 μ)²`. -/
private theorem ofReal_integral_normSq_le_eLpNorm_sq_aux {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F H : α → ℂ} {M : ℝ}
    (_hM : 0 ≤ M) (hFint : Integrable (fun z => ‖F z‖ ^ 2) μ)
    (hbd : ∀ z, ‖F z‖ ≤ M * ‖H z‖) :
    ENNReal.ofReal (∫ z, ‖F z‖ ^ 2 ∂μ)
      ≤ ENNReal.ofReal (M ^ 2) * (eLpNorm H 2 μ) ^ 2 := by
  -- Convert the Bochner integral of `‖F‖²` into a Lebesgue integral of `‖F‖ₑ²`.
  have hconv : ENNReal.ofReal (∫ z, ‖F z‖ ^ 2 ∂μ) = ∫⁻ z, ‖F z‖ₑ ^ (2:ℝ) ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hFint
      (Filter.Eventually.of_forall fun z => sq_nonneg ‖F z‖)]
    exact lintegral_congr fun z => (enorm_sq_eq_ofReal' (F z)).symm
  rw [hconv]
  -- `(eLpNorm H 2 μ)²` dominates the Lebesgue integral of `‖H‖ₑ²`.
  have hkey : ∫⁻ z, ‖H z‖ₑ ^ (2:ℝ) ∂μ ≤ (eLpNorm H 2 μ) ^ 2 := by
    by_cases hh : AEStronglyMeasurable H μ
    · have h1 := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := H) (p := (2:NNReal))
        (by norm_num) hh
      simp only [show ((2:NNReal):ℝ) = 2 from by norm_num] at h1
      rw [← h1]
      norm_num
    · rw [eLpNorm_of_not_aestronglyMeasurable hh]
      simp
  calc ∫⁻ z, ‖F z‖ₑ ^ (2:ℝ) ∂μ
      ≤ ∫⁻ z, ENNReal.ofReal (M ^ 2) * ‖H z‖ₑ ^ (2:ℝ) ∂μ :=
        lintegral_mono fun z => by
          rw [enorm_sq_eq_ofReal', enorm_sq_eq_ofReal', ← ENNReal.ofReal_mul (sq_nonneg M)]
          apply ENNReal.ofReal_le_ofReal
          have h := pow_le_pow_left₀ (norm_nonneg (F z)) (hbd z) 2
          rwa [mul_pow] at h
    _ = ENNReal.ofReal (M ^ 2) * ∫⁻ z, ‖H z‖ₑ ^ (2:ℝ) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (M ^ 2) * (eLpNorm H 2 μ) ^ 2 := mul_le_mul_right hkey _

theorem ofReal_integral_normSq_le_eLpNorm_sq {n : ℕ} {ρ : Fin n → ℝ}
    {G h : Work.NN.Core.Cn n → ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hG : ContDiff ℝ 1 G) (hGcs : HasCompactSupport G)
    (hGsupp : tsupport G ⊆ Work.CR.Flat.polydisc 0 ρ) (hbd : ∀ z, ‖G z‖ ≤ M * ‖h z‖) :
    ENNReal.ofReal (∫ z, ‖G z‖ ^ 2)
      ≤ ENNReal.ofReal (M ^ 2) *
        (MeasureTheory.eLpNorm h 2 (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ))) ^ 2 := by
  -- `‖G‖²` is continuous with compact support, hence integrable.
  have hint : Integrable (fun z : Work.NN.Core.Cn n => ‖G z‖ ^ 2) volume := by
    have hc : Continuous (fun z : Work.NN.Core.Cn n => ‖G z‖ ^ 2) := (hG.continuous.norm).pow 2
    have hcs : HasCompactSupport (fun z : Work.NN.Core.Cn n => ‖G z‖ ^ 2) :=
      hGcs.norm.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
    exact hc.integrable_of_hasCompactSupport hcs
  -- `G` vanishes off its support, which is contained in the polydisc, so the integral over
  -- `volume` is the integral over `volume.restrict (polydisc 0 ρ)`.
  have hsupp : (∫ z, ‖G z‖ ^ 2) =
      ∫ z, ‖G z‖ ^ 2 ∂(volume.restrict (Work.CR.Flat.polydisc 0 ρ)) := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (s := Work.CR.Flat.polydisc 0 ρ) ?_).symm
    intro z hz
    have hGz : G z = 0 := by
      by_contra hne
      exact hz (hGsupp (subset_closure (Function.mem_support.mpr hne)))
    simp [hGz]
  rw [hsupp]
  exact ofReal_integral_normSq_le_eLpNorm_sq_aux hM hint.restrict hbd

end Work.NN.Core
