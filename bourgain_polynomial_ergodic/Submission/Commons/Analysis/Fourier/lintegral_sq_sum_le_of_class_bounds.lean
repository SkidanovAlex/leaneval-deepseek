import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

namespace Commons.Analysis.Fourier

open scoped BigOperators ENNReal
open MeasureTheory

theorem lintegral_sq_sum_le_of_class_bounds {ι : Type*} (s : Finset ι)
    (A : ι → ℝ → ℝ) (u : ι → ℝ) (hu : ∀ i ∈ s, 0 < u i)
    (hAnn : ∀ i ∈ s, ∀ y : ℝ, 0 ≤ A i y)
    (hmeas : ∀ i ∈ s, AEMeasurable (fun y => ENNReal.ofReal (A i y) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (0:ℝ) 1)))
    (hA : ∀ i ∈ s, ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (A i y) ^ 2
      ≤ ENNReal.ofReal ((u i) ^ 2)) :
    ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal ((∑ i ∈ s, A i y)) ^ 2
      ≤ ENNReal.ofReal ((∑ i ∈ s, u i) ^ 2) := by
  classical
  set μ : MeasureTheory.Measure ℝ :=
    (MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Ioc (0:ℝ) 1) with hμ
  -- Measurability of each `A i` (as a real-valued function, w.r.t. μ).
  have hAi_meas : ∀ i ∈ s, AEMeasurable (fun y => A i y) μ := by
    intro i hi
    have hsq : ∀ y, ENNReal.ofReal (A i y) ^ 2 = ENNReal.ofReal ((A i y) ^ 2) := by
      intro y
      rw [pow_two, ← ENNReal.ofReal_mul (hAnn i hi y)]
      congr 1
      ring
    have hG' : AEMeasurable (fun y => ENNReal.ofReal ((A i y) ^ 2)) μ :=
      (hmeas i hi).congr (Filter.Eventually.of_forall hsq)
    have h1 : AEMeasurable (fun y => (ENNReal.ofReal ((A i y) ^ 2)).toReal) μ :=
      ENNReal.measurable_toReal.comp_aemeasurable hG'
    have h2 : AEMeasurable (fun y => (A i y) ^ 2) μ :=
      h1.congr (Filter.Eventually.of_forall (fun y => ENNReal.toReal_ofReal (sq_nonneg _)))
    have h3 : AEMeasurable (fun y => Real.sqrt ((A i y) ^ 2)) μ :=
      (Continuous.measurable Real.continuous_sqrt).comp_aemeasurable h2
    exact h3.congr (Filter.Eventually.of_forall (fun y => Real.sqrt_sq (hAnn i hi y)))
  have hf_meas : ∀ i ∈ s, AEMeasurable (fun y => ENNReal.ofReal (A i y)) μ :=
    fun i hi => ENNReal.measurable_ofReal.comp_aemeasurable (hAi_meas i hi)
  -- Termwise Cauchy–Schwarz bound.
  have hterm : ∀ i ∈ s, ∀ j ∈ s,
      ∫⁻ y, ENNReal.ofReal (A i y) * ENNReal.ofReal (A j y) ∂μ
        ≤ ENNReal.ofReal (u i * u j) := by
    intro i hi j hj
    have h_holder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (p := 2) (q := 2)
      Real.HolderConjugate.two_two (hf_meas i hi) (hf_meas j hj)
    have hgi_eq : (∫⁻ a, ENNReal.ofReal (A i a) ^ (2:ℝ) ∂μ)
        = ∫⁻ a, ENNReal.ofReal (A i a) ^ 2 ∂μ :=
      lintegral_congr_ae (Filter.Eventually.of_forall (fun a => ENNReal.rpow_two _))
    have hgj_eq : (∫⁻ a, ENNReal.ofReal (A j a) ^ (2:ℝ) ∂μ)
        = ∫⁻ a, ENNReal.ofReal (A j a) ^ 2 ∂μ :=
      lintegral_congr_ae (Filter.Eventually.of_forall (fun a => ENNReal.rpow_two _))
    rw [hgi_eq, hgj_eq] at h_holder
    have hbi : (∫⁻ y, ENNReal.ofReal (A i y) ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (u i) := by
      calc (∫⁻ y, ENNReal.ofReal (A i y) ^ 2 ∂μ) ^ (1 / 2 : ℝ)
          ≤ (ENNReal.ofReal (u i ^ 2)) ^ (1 / 2 : ℝ) :=
            ENNReal.rpow_le_rpow (hA i hi) (by norm_num)
        _ = ENNReal.ofReal (u i) := by
            rw [ENNReal.ofReal_rpow_of_nonneg (x := u i ^ 2) (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 1 / 2)]
            congr 1
            rw [← Real.sqrt_eq_rpow]
            exact Real.sqrt_sq (hu i hi).le
    have hbj : (∫⁻ y, ENNReal.ofReal (A j y) ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (u j) := by
      calc (∫⁻ y, ENNReal.ofReal (A j y) ^ 2 ∂μ) ^ (1 / 2 : ℝ)
          ≤ (ENNReal.ofReal (u j ^ 2)) ^ (1 / 2 : ℝ) :=
            ENNReal.rpow_le_rpow (hA j hj) (by norm_num)
        _ = ENNReal.ofReal (u j) := by
            rw [ENNReal.ofReal_rpow_of_nonneg (x := u j ^ 2) (sq_nonneg _) (by norm_num : (0:ℝ) ≤ 1 / 2)]
            congr 1
            rw [← Real.sqrt_eq_rpow]
            exact Real.sqrt_sq (hu j hj).le
    refine h_holder.trans ?_
    calc (∫⁻ y, ENNReal.ofReal (A i y) ^ 2 ∂μ) ^ (1 / 2 : ℝ)
            * (∫⁻ y, ENNReal.ofReal (A j y) ^ 2 ∂μ) ^ (1 / 2 : ℝ)
        ≤ ENNReal.ofReal (u i) * ENNReal.ofReal (u j) :=
          mul_le_mul hbi hbj zero_le zero_le
      _ = ENNReal.ofReal (u i * u j) := (ENNReal.ofReal_mul (hu i hi).le).symm
  -- Sum of the termwise bounds.
  have hR : (∑ i ∈ s, ∑ j ∈ s, ENNReal.ofReal (u i * u j))
      = ENNReal.ofReal ((∑ i ∈ s, u i) ^ 2) := by
    have hsum_real : (∑ i ∈ s, ∑ j ∈ s, u i * u j) = (∑ i ∈ s, u i) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum]
    have hinner : ∀ i ∈ s,
        (∑ j ∈ s, ENNReal.ofReal (u i * u j)) = ENNReal.ofReal (∑ j ∈ s, u i * u j) := by
      intro i hi
      rw [ENNReal.ofReal_sum_of_nonneg (fun j hj => mul_nonneg (hu i hi).le (hu j hj).le)]
    calc (∑ i ∈ s, ∑ j ∈ s, ENNReal.ofReal (u i * u j))
        = ∑ i ∈ s, ENNReal.ofReal (∑ j ∈ s, u i * u j) :=
          Finset.sum_congr rfl (fun i hi => hinner i hi)
      _ = ENNReal.ofReal (∑ i ∈ s, ∑ j ∈ s, u i * u j) := by
          rw [ENNReal.ofReal_sum_of_nonneg (f := fun i => ∑ j ∈ s, u i * u j)
            (fun i hi => Finset.sum_nonneg (fun j hj => mul_nonneg (hu i hi).le (hu j hj).le))]
      _ = ENNReal.ofReal ((∑ i ∈ s, u i) ^ 2) := by rw [hsum_real]
  -- Main bound on the square of the sum.
  have hmain : ∫⁻ y, (∑ i ∈ s, ENNReal.ofReal (A i y)) ^ 2 ∂μ
      ≤ ENNReal.ofReal ((∑ i ∈ s, u i) ^ 2) := by
    have hsq_sum : ∀ y, (∑ i ∈ s, ENNReal.ofReal (A i y)) ^ 2
        = ∑ i ∈ s, ∑ j ∈ s, ENNReal.ofReal (A i y) * ENNReal.ofReal (A j y) := by
      intro y
      rw [pow_two, Finset.sum_mul_sum]
    rw [lintegral_congr_ae (Filter.Eventually.of_forall hsq_sum)]
    have hmeas_inner : ∀ i ∈ s, AEMeasurable
        (fun y => (∑ j ∈ s, ENNReal.ofReal (A i y) * ENNReal.ofReal (A j y))) μ := by
      intro i hi
      have h := Finset.aemeasurable_sum s (fun j hj => (hf_meas i hi).mul (hf_meas j hj))
      convert h using 1
      ext y
      simp only [Pi.mul_apply, Finset.sum_apply]
    calc ∫⁻ y, (∑ i ∈ s, ∑ j ∈ s,
            ENNReal.ofReal (A i y) * ENNReal.ofReal (A j y)) ∂μ
        = ∑ i ∈ s, ∫⁻ y, (∑ j ∈ s,
            ENNReal.ofReal (A i y) * ENNReal.ofReal (A j y)) ∂μ :=
          lintegral_finsetSum' s hmeas_inner
      _ = ∑ i ∈ s, ∑ j ∈ s,
            ∫⁻ y, ENNReal.ofReal (A i y) * ENNReal.ofReal (A j y) ∂μ := by
          apply Finset.sum_congr rfl
          intro i hi
          exact lintegral_finsetSum' s (fun j hj => (hf_meas i hi).mul (hf_meas j hj))
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, ENNReal.ofReal (u i * u j) :=
          Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hterm i hi j hj))
      _ = ENNReal.ofReal ((∑ i ∈ s, u i) ^ 2) := hR
  -- Convert the integrand back.
  have hmain2 : ∫⁻ y, ENNReal.ofReal (∑ i ∈ s, A i y) ^ 2 ∂μ
      ≤ ENNReal.ofReal ((∑ i ∈ s, u i) ^ 2) := by
    have heq : ∫⁻ y, ENNReal.ofReal (∑ i ∈ s, A i y) ^ 2 ∂μ
        = ∫⁻ y, (∑ i ∈ s, ENNReal.ofReal (A i y)) ^ 2 ∂μ := by
      apply lintegral_congr_ae
      filter_upwards with y
      rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => hAnn i hi y)]
    rw [heq]
    exact hmain
  exact hmain2

end Commons.Analysis.Fourier