import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Submission.Commons.Analysis.Integral.exists_dual_witness
import Submission.Commons.Analysis.Integral.holder_complex_finset

namespace Commons.Analysis.Integral

open MeasureTheory
open scoped BigOperators ENNReal

theorem ellp_integral_minkowski {J : ℕ} {s : ℝ} (hs : 1 ≤ s)
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    (f : Fin J → α → ℂ) (hf : ∀ j, MeasureTheory.AEStronglyMeasurable (f j) μ)
    (hb : ∃ C : ℝ, ∀ j : Fin J, ∀ᵐ a ∂μ, ‖f j a‖ ≤ C) :
    (∑ j : Fin J, ‖∫ a, f j a ∂μ‖ ^ s) ^ (1 / s)
      ≤ ∫ a, (∑ j : Fin J, ‖f j a‖ ^ s) ^ (1 / s) ∂μ := by
  classical
  obtain ⟨C, hC⟩ := hb
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hInt : ∀ j : Fin J, Integrable (f j) μ := fun j => Integrable.of_bound (hf j) C (hC j)
  have hbdd : ∀ᵐ a ∂μ, ∀ j : Fin J, ‖f j a‖ ≤ max C 0 := by
    rw [Filter.eventually_all]
    intro j
    filter_upwards [hC j] with a ha
    exact ha.trans (le_max_left _ _)
  rcases eq_or_lt_of_le hs with h1 | hgt
  · -- s = 1
    rw [← h1]
    simp only [div_one, Real.rpow_one]
    calc ∑ j : Fin J, ‖∫ a, f j a ∂μ‖
        ≤ ∑ j : Fin J, ∫ a, ‖f j a‖ ∂μ :=
          Finset.sum_le_sum (fun j _ => norm_integral_le_integral_norm (f j))
      _ = ∫ a, ∑ j : Fin J, ‖f j a‖ ∂μ :=
          (integral_finsetSum Finset.univ (fun j _ => (hInt j).norm)).symm
  · -- 1 < s
    have hsne : s ≠ 0 := by linarith
    have hs1ne : s - 1 ≠ 0 := by linarith
    have hpq : s.HolderConjugate (s / (s - 1)) := by
      rw [Real.holderConjugate_iff]
      refine ⟨hgt, ?_⟩
      rw [inv_div]
      field_simp
      ring
    have hs_sum : 1 / s + 1 / (s / (s - 1)) = 1 := by
      rw [one_div, one_div]
      exact hpq.inv_add_inv_eq_one
    have hs'_gt : 1 < s / (s - 1) := by
      rw [lt_div_iff₀ (by linarith : (0:ℝ) < s - 1)]
      linarith
    by_cases hu : (fun j : Fin J => ∫ a, f j a ∂μ) = 0
    · -- all integrals vanish
      have hzero : (∑ j : Fin J, ‖∫ a, f j a ∂μ‖ ^ s) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have hj0 : (∫ a, f j a ∂μ) = 0 := by
          have := congr_fun hu j
          simpa using this
        rw [hj0, norm_zero, Real.zero_rpow (ne_of_gt hs_pos)]
      rw [hzero, Real.zero_rpow (ne_of_gt (by positivity : (0:ℝ) < 1 / s))]
      exact integral_nonneg
        (fun a => Real.rpow_nonneg (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (norm_nonneg _) s)) _)
    · -- duality
      obtain ⟨g, hg_norm, hg_dual⟩ :=
        exists_dual_witness hgt hs'_gt hs_sum (fun j => ∫ a, f j a ∂μ) hu
      have hlin : ∑ j : Fin J, (∫ a, f j a ∂μ) * g j
          = ∫ a, ∑ j : Fin J, f j a * g j ∂μ := by
        rw [integral_finsetSum Finset.univ (fun j _ => (hInt j).mul_const (g j))]
        exact Finset.sum_congr rfl (fun j _ => (integral_mul_const (g j) (f j)).symm)
      have hLint : Integrable (fun a => ‖∑ j : Fin J, f j a * g j‖) μ := by
        refine Integrable.of_bound ?_ (∑ j : Fin J, max C 0 * ‖g j‖) ?_
        · have h0 : AEStronglyMeasurable (fun a => ∑ j : Fin J, f j a * g j) μ := by
            have h := Finset.aestronglyMeasurable_sum Finset.univ
              (f := fun j a => f j a * g j) (fun j _ => (hf j).mul_const (g j))
            rw [Finset.sum_fn] at h
            exact h
          exact h0.norm
        · filter_upwards [hbdd] with a ha
          calc ‖‖∑ j : Fin J, f j a * g j‖‖
              = ‖∑ j : Fin J, f j a * g j‖ := Real.norm_of_nonneg (norm_nonneg _)
            _ ≤ ∑ j : Fin J, ‖f j a * g j‖ := norm_sum_le _ _
            _ = ∑ j : Fin J, ‖f j a‖ * ‖g j‖ := by simp only [norm_mul]
            _ ≤ ∑ j : Fin J, max C 0 * ‖g j‖ :=
                Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (ha j) (norm_nonneg _))
      have hRint : Integrable (fun a => (∑ j : Fin J, ‖f j a‖ ^ s) ^ (1 / s)) μ := by
        refine Integrable.of_bound ?_ ((∑ j : Fin J, (max C 0) ^ s) ^ (1 / s)) ?_
        · apply AEMeasurable.aestronglyMeasurable
          have hinner : AEMeasurable (fun a => ∑ j : Fin J, ‖f j a‖ ^ s) μ := by
            have h := Finset.aemeasurable_sum Finset.univ (f := fun j a => ‖f j a‖ ^ s)
              (fun j _ => (Real.continuous_rpow_const hs_pos.le).measurable.comp_aemeasurable
                ((hf j).norm.aemeasurable))
            rw [Finset.sum_fn] at h
            exact h
          exact (Real.continuous_rpow_const (by positivity : (0:ℝ) ≤ 1 / s)).measurable.comp_aemeasurable
            hinner
        · filter_upwards [hbdd] with a ha
          have hnonneg : 0 ≤ ∑ j : Fin J, ‖f j a‖ ^ s :=
            Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (norm_nonneg _) s)
          calc ‖(∑ j : Fin J, ‖f j a‖ ^ s) ^ (1 / s)‖
              = (∑ j : Fin J, ‖f j a‖ ^ s) ^ (1 / s) :=
                Real.norm_of_nonneg (Real.rpow_nonneg hnonneg _)
            _ ≤ (∑ j : Fin J, (max C 0) ^ s) ^ (1 / s) :=
                Real.rpow_le_rpow hnonneg
                  (Finset.sum_le_sum (fun j _ => Real.rpow_le_rpow (norm_nonneg _) (ha j) hs_pos.le))
                  (by positivity)
      calc (∑ j : Fin J, ‖∫ a, f j a ∂μ‖ ^ s) ^ (1 / s)
          ≤ ‖∑ j : Fin J, (∫ a, f j a ∂μ) * g j‖ := hg_dual
        _ = ‖∫ a, ∑ j : Fin J, f j a * g j ∂μ‖ := by rw [hlin]
        _ ≤ ∫ a, ‖∑ j : Fin J, f j a * g j‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ ∫ a, (∑ j : Fin J, ‖f j a‖ ^ s) ^ (1 / s) ∂μ :=
            integral_mono hLint hRint (fun a =>
              (holder_complex_finset Finset.univ (fun j => f j a) g hpq).trans_eq
                (by rw [hg_norm, mul_one]))

end Commons.Analysis.Integral