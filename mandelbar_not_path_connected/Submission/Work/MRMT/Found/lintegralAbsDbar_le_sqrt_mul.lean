import Mathlib
import Submission.Work.MRMT.Found.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Filter Topology Complex Function
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Found

/-- **Hölder/Cauchy–Schwarz bound for `∫⁻ ‖∂̄F‖`.**

If `∂̄F = μF · ∂F` pointwise and `μF` is a.e. strongly measurable with `‖μF‖ ≤ C`, then on a
compact set `L` the `L¹`-size of `∂̄F` is controlled by the product of the `L²` norms of `μF`
and of `∂F`:
`∫⁻_L ‖∂̄F‖ ≤ √(∫_L ‖μF‖²) · √(∫_L ‖∂F‖²)`.

(The compactness of `L` is what makes the two `L²` quantities finite and hence makes the
Bochner integrals in the statement agree with the corresponding `lintegral`s.) -/
theorem lintegralAbsDbar_le_sqrt_mul {F μF : ℂ → ℂ}
    (hμmeas : MeasureTheory.AEStronglyMeasurable μF (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    {C : ℝ} (hC : ∀ z : ℂ, ‖μF z‖ ≤ C)
    (hF : ContDiff ℝ 1 F) (hrel : ∀ z : ℂ, Work.MRMT.dzbar F z = μF z * Work.MRMT.dz F z)
    {L : Set ℂ} (hL : IsCompact L) :
    lintegralAbsDbar F L ≤
      ENNReal.ofReal (Real.sqrt (∫ z in L, ‖μF z‖ ^ 2) * Real.sqrt (∫ z in L, ‖Work.MRMT.dz F z‖ ^ 2)) := by
  -- the restriction of Lebesgue measure to the compact set `L` is a finite measure
  have hfinL : IsFiniteMeasure ((volume : Measure ℂ).restrict L) := by
    rw [isFiniteMeasure_iff, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hL.measure_lt_top
  -- `∂F` is continuous, hence bounded on the compact set `L`
  have hdzc : Continuous (fun z : ℂ => Work.MRMT.dz F z) := by
    have hfderiv : Continuous (fun z : ℂ => fderiv ℝ F z) := hF.continuous_fderiv (by norm_num)
    unfold Work.MRMT.dz
    exact ((hfderiv.clm_apply continuous_const).sub
      (continuous_const.mul (hfderiv.clm_apply continuous_const))).div_const 2
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn hdzc.continuousOn
  -- a.e. measurability of the two Hölder factors
  have ha : AEMeasurable (fun z : ℂ => ENNReal.ofReal ‖μF z‖) ((volume : Measure ℂ).restrict L) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hμmeas.norm.aemeasurable).restrict)
  have hb : AEMeasurable (fun z : ℂ => ENNReal.ofReal ‖Work.MRMT.dz F z‖)
      ((volume : Measure ℂ).restrict L) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hdzc.norm.aestronglyMeasurable.restrict).aemeasurable)
  -- integrability of the two squares on `L`
  have hint1 : Integrable (fun z : ℂ => ‖μF z‖ ^ 2) ((volume : Measure ℂ).restrict L) :=
    Integrable.of_bound
      (((continuous_pow 2).comp_aestronglyMeasurable hμmeas.norm).restrict) (C ^ 2) (by
        filter_upwards with z
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC z) 2)
  have hint2 : Integrable (fun z : ℂ => ‖Work.MRMT.dz F z‖ ^ 2) ((volume : Measure ℂ).restrict L) :=
    Integrable.of_bound
      (((continuous_pow 2).comp_aestronglyMeasurable hdzc.norm.aestronglyMeasurable).restrict)
      (M ^ 2) (by
        filter_upwards [ae_restrict_mem hL.measurableSet] with z hz
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hM z hz) 2)
  -- the pointwise conversion `(ofReal ‖·‖)^2 = ofReal (‖·‖^2)`
  have hpoint1 : ∀ z : ℂ,
      (ENNReal.ofReal ‖μF z‖) ^ (2 : ℝ) = ENNReal.ofReal (‖μF z‖ ^ 2) := fun z =>
    calc (ENNReal.ofReal ‖μF z‖) ^ (2 : ℝ)
        = (ENNReal.ofReal ‖μF z‖) ^ (2 : ℕ) := ENNReal.rpow_natCast _ 2
      _ = ENNReal.ofReal (‖μF z‖ ^ 2) := (ENNReal.ofReal_pow (norm_nonneg (μF z)) 2).symm
  have hpoint2 : ∀ z : ℂ,
      (ENNReal.ofReal ‖Work.MRMT.dz F z‖) ^ (2 : ℝ)
        = ENNReal.ofReal (‖Work.MRMT.dz F z‖ ^ 2) := fun z =>
    calc (ENNReal.ofReal ‖Work.MRMT.dz F z‖) ^ (2 : ℝ)
        = (ENNReal.ofReal ‖Work.MRMT.dz F z‖) ^ (2 : ℕ) := ENNReal.rpow_natCast _ 2
      _ = ENNReal.ofReal (‖Work.MRMT.dz F z‖ ^ 2) :=
          (ENNReal.ofReal_pow (norm_nonneg (Work.MRMT.dz F z)) 2).symm
  -- `∫⁻` of the square of the modulus is the `ofReal` of the Bochner integral of the square
  have hsq1 : (∫⁻ z in L, (ENNReal.ofReal ‖μF z‖) ^ (2 : ℝ))
      = ENNReal.ofReal (∫ z in L, ‖μF z‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint1 (Eventually.of_forall (fun z => sq_nonneg _))]
    exact lintegral_congr hpoint1
  have hsq2 : (∫⁻ z in L, (ENNReal.ofReal ‖Work.MRMT.dz F z‖) ^ (2 : ℝ))
      = ENNReal.ofReal (∫ z in L, ‖Work.MRMT.dz F z‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint2 (Eventually.of_forall (fun z => sq_nonneg _))]
    exact lintegral_congr hpoint2
  -- the two Hölder factors in the shape of the statement
  have hfac1 : (∫⁻ z in L, (ENNReal.ofReal ‖μF z‖) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (Real.sqrt (∫ z in L, ‖μF z‖ ^ 2)) := by
    rw [hsq1, Real.sqrt_eq_rpow]
    exact ENNReal.ofReal_rpow_of_nonneg
      (integral_nonneg_of_ae (Eventually.of_forall (fun z => sq_nonneg _))) (by norm_num)
  have hfac2 : (∫⁻ z in L, (ENNReal.ofReal ‖Work.MRMT.dz F z‖) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (Real.sqrt (∫ z in L, ‖Work.MRMT.dz F z‖ ^ 2)) := by
    rw [hsq2, Real.sqrt_eq_rpow]
    exact ENNReal.ofReal_rpow_of_nonneg
      (integral_nonneg_of_ae (Eventually.of_forall (fun z => sq_nonneg _))) (by norm_num)
  -- Hölder's inequality with exponents `p = q = 2`
  have holder : (∫⁻ z in L, ENNReal.ofReal ‖μF z‖ * ENNReal.ofReal ‖Work.MRMT.dz F z‖) ≤
      (∫⁻ z in L, (ENNReal.ofReal ‖μF z‖) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        * (∫⁻ z in L, (ENNReal.ofReal ‖Work.MRMT.dz F z‖) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ((volume : Measure ℂ).restrict L)
      Real.HolderConjugate.two_two ha hb
    simpa using h
  calc lintegralAbsDbar F L
      = ∫⁻ z in L, ENNReal.ofReal (‖μF z‖ * ‖Work.MRMT.dz F z‖) := by
        unfold lintegralAbsDbar
        exact lintegral_congr (fun z => by rw [hrel z, norm_mul])
    _ = ∫⁻ z in L, ENNReal.ofReal ‖μF z‖ * ENNReal.ofReal ‖Work.MRMT.dz F z‖ := by
        refine lintegral_congr (fun z => ?_)
        rw [ENNReal.ofReal_mul (norm_nonneg _)]
    _ ≤ (∫⁻ z in L, (ENNReal.ofReal ‖μF z‖) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
          * (∫⁻ z in L, (ENNReal.ofReal ‖Work.MRMT.dz F z‖) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := holder
    _ = ENNReal.ofReal (Real.sqrt (∫ z in L, ‖μF z‖ ^ 2))
          * ENNReal.ofReal (Real.sqrt (∫ z in L, ‖Work.MRMT.dz F z‖ ^ 2)) := by
        rw [hfac1, hfac2]
    _ = ENNReal.ofReal (Real.sqrt (∫ z in L, ‖μF z‖ ^ 2)
          * Real.sqrt (∫ z in L, ‖Work.MRMT.dz F z‖ ^ 2)) :=
        (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm

end Work.MRMT.Found
