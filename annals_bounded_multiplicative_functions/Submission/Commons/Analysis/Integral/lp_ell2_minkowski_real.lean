import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.Commons.Analysis.Integral.aemeasurable_of_nonneg_rpow
import Submission.Commons.Analysis.Integral.lintegral_mul_le_rpow
import Submission.Commons.Analysis.Integral.rpow_le_sqrt_of_le_rpow_mul_real

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Integral

open scoped BigOperators
open MeasureTheory
open scoped ENNReal

open MeasureTheory in
theorem lp_ell2_minkowski_real {α : Type*} [MeasurableSpace α] (μ : Measure α) {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 2 ≤ p) {F : ι → α → ℝ} (hF : ∀ i x, 0 ≤ F i x)
    (hint : ∀ i, Integrable (fun x => (F i x) ^ p) μ)
    (hint2 : Integrable (fun x => (∑ i, (F i x) ^ 2) ^ (p / 2)) μ) :
    (∫ x, (∑ i, (F i x) ^ 2) ^ (p / 2) ∂μ) ^ (1 / p)
      ≤ (∑ i, (∫ x, (F i x) ^ p ∂μ) ^ (2 / p)) ^ ((1 : ℝ) / 2) := by
  classical
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hFi_meas : ∀ i, AEMeasurable (F i) μ := fun i =>
    aemeasurable_of_nonneg_rpow (hF i) hp_pos (hint i).aemeasurable
  by_cases hp2 : p = 2
  · subst p
    have hs_int : Integrable (fun x => ∑ i, (F i x) ^ 2) μ := by
      refine hint2.congr ?_
      filter_upwards with x
      rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
    have hFi2_int : ∀ i, Integrable (fun x => (F i x) ^ 2) μ := by
      intro i
      refine Integrable.mono' hs_int ((hFi_meas i).pow_const 2).aestronglyMeasurable ?_
      filter_upwards with x
      rw [Real.norm_of_nonneg (sq_nonneg (F i x))]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (F j x)) (Finset.mem_univ i)
    have hsum : ∫ x, (∑ i, (F i x) ^ 2) ∂μ = ∑ i, ∫ x, (F i x) ^ 2 ∂μ :=
      integral_finsetSum Finset.univ (fun i _ => hFi2_int i)
    simp only [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one, Real.rpow_ofNat]
    rw [hsum]
  · have hp2lt : 2 < p := lt_of_le_of_ne hp (Ne.symm hp2)
    let s : α → ℝ := fun x => ∑ i, (F i x) ^ 2
    let G : α → ℝ := fun x => s x ^ (p / 2)
    let H : α → ℝ := fun x => s x ^ ((p - 2) / 2)
    change (∫ x, G x ∂μ) ^ (1 / p)
      ≤ (∑ i, (∫ x, (F i x) ^ p ∂μ) ^ (2 / p)) ^ ((1 : ℝ) / 2)
    have hs_nn : ∀ x, 0 ≤ s x := fun x => Finset.sum_nonneg fun i _ => sq_nonneg (F i x)
    have hG_nn : ∀ x, 0 ≤ G x := fun x => Real.rpow_nonneg (hs_nn x) _
    have hH_nn : ∀ x, 0 ≤ H x := fun x => Real.rpow_nonneg (hs_nn x) _
    have hs_meas : AEMeasurable s μ := by
      show AEMeasurable (fun x => ∑ i, (F i x) ^ 2) μ
      fun_prop
    have hH_meas : AEMeasurable H μ := by
      show AEMeasurable (fun x => s x ^ ((p - 2) / 2)) μ
      exact hs_meas.pow_const _
    have hFi2_meas : ∀ i, AEMeasurable (fun x => (F i x) ^ 2) μ := fun i => by fun_prop
    have hHFi_pt : ∀ (i : ι) (x : α), H x ^ (p / (p - 2)) = G x := by
      intro i x
      show (s x ^ ((p - 2) / 2)) ^ (p / (p - 2)) = s x ^ (p / 2)
      rw [← Real.rpow_mul (hs_nn x)]
      congr 1
      field_simp
    have hFi_pt : ∀ (i : ι) (x : α), ((F i x) ^ 2) ^ (p / 2) = (F i x) ^ p := by
      intro i x
      rw [show ((F i x) ^ 2 : ℝ) = (F i x) ^ (2 : ℝ) by rw [Real.rpow_ofNat]]
      rw [← Real.rpow_mul (hF i x)]
      congr 1
      ring
    have hper : ∀ i, ∫⁻ x, ENNReal.ofReal (H x * (F i x) ^ 2) ∂μ ≤
        (∫⁻ x, ENNReal.ofReal (G x) ∂μ) ^ ((p - 2) / p) *
          (∫⁻ x, ENNReal.ofReal ((F i x) ^ p) ∂μ) ^ (2 / p) := by
      intro i
      have hb := lintegral_mul_le_rpow μ hp2lt hH_nn (fun x => sq_nonneg (F i x))
        hH_meas (hFi2_meas i)
      have h1 : ∫⁻ x, ENNReal.ofReal (H x ^ (p / (p - 2))) ∂μ =
          ∫⁻ x, ENNReal.ofReal (G x) ∂μ := by
        apply lintegral_congr; intro x; rw [hHFi_pt i x]
      have h2 : ∫⁻ x, ENNReal.ofReal (((F i x) ^ 2) ^ (p / 2)) ∂μ =
          ∫⁻ x, ENNReal.ofReal ((F i x) ^ p) ∂μ := by
        apply lintegral_congr; intro x; rw [hFi_pt i x]
      rw [h1, h2] at hb
      exact hb
    have hpt : ∀ x, ENNReal.ofReal (G x) = ∑ i, ENNReal.ofReal (H x * (F i x) ^ 2) := by
      intro x
      have h1 : G x = ∑ i, H x * (F i x) ^ 2 := by
        have h2 : G x = H x * s x := by
          show s x ^ (p / 2) = s x ^ ((p - 2) / 2) * s x
          rw [show p / 2 = (p - 2) / 2 + 1 by ring,
            Real.rpow_add_of_nonneg (hs_nn x) (by positivity) (by norm_num), Real.rpow_one]
        rw [h2]
        change H x * (∑ i, (F i x) ^ 2) = ∑ i, H x * (F i x) ^ 2
        rw [Finset.mul_sum]
      rw [h1, ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hH_nn x) (sq_nonneg _))]
    have hsum : ∫⁻ x, ENNReal.ofReal (G x) ∂μ =
        ∑ i, ∫⁻ x, ENNReal.ofReal (H x * (F i x) ^ 2) ∂μ := by
      calc ∫⁻ x, ENNReal.ofReal (G x) ∂μ
          = ∫⁻ x, ∑ i, ENNReal.ofReal (H x * (F i x) ^ 2) ∂μ := by
            apply lintegral_congr; exact hpt
        _ = ∑ i, ∫⁻ x, ENNReal.ofReal (H x * (F i x) ^ 2) ∂μ := by
            apply lintegral_finsetSum'
            intro i _
            exact (hH_meas.mul (hFi2_meas i)).ennreal_ofReal
    have hchain : ∫⁻ x, ENNReal.ofReal (G x) ∂μ ≤
        (∫⁻ x, ENNReal.ofReal (G x) ∂μ) ^ ((p - 2) / p) *
          ∑ i, (∫⁻ x, ENNReal.ofReal ((F i x) ^ p) ∂μ) ^ (2 / p) := by
      calc ∫⁻ x, ENNReal.ofReal (G x) ∂μ
          = ∑ i, ∫⁻ x, ENNReal.ofReal (H x * (F i x) ^ 2) ∂μ := hsum
        _ ≤ ∑ i, (∫⁻ x, ENNReal.ofReal (G x) ∂μ) ^ ((p - 2) / p) *
                (∫⁻ x, ENNReal.ofReal ((F i x) ^ p) ∂μ) ^ (2 / p) :=
            Finset.sum_le_sum (fun i _ => hper i)
        _ = (∫⁻ x, ENNReal.ofReal (G x) ∂μ) ^ ((p - 2) / p) *
              ∑ i, (∫⁻ x, ENNReal.ofReal ((F i x) ^ p) ∂μ) ^ (2 / p) := by
            rw [Finset.mul_sum]
    have hAe_eq : ∫⁻ x, ENNReal.ofReal (G x) ∂μ = ENNReal.ofReal (∫ x, G x ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hint2 (ae_of_all μ hG_nn)).symm
    have hbe_eq : ∀ i, ∫⁻ x, ENNReal.ofReal ((F i x) ^ p) ∂μ =
        ENNReal.ofReal (∫ x, (F i x) ^ p ∂μ) := fun i =>
      (ofReal_integral_eq_lintegral_ofReal (hint i)
        (ae_of_all μ (fun x => Real.rpow_nonneg (hF i x) p))).symm
    have hA_nn : 0 ≤ ∫ x, G x ∂μ := integral_nonneg hG_nn
    have hAi_nn : ∀ i, 0 ≤ ∫ x, (F i x) ^ p ∂μ :=
      fun i => integral_nonneg (fun x => Real.rpow_nonneg (hF i x) p)
    have hB_nn : 0 ≤ ∑ i, (∫ x, (F i x) ^ p ∂μ) ^ (2 / p) :=
      Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hAi_nn i) _)
    have hReal : ∫ x, G x ∂μ ≤ (∫ x, G x ∂μ) ^ ((p - 2) / p) *
        ∑ i, (∫ x, (F i x) ^ p ∂μ) ^ (2 / p) := by
      rw [hAe_eq] at hchain
      simp_rw [hbe_eq] at hchain
      have hsumconv : ∑ i, (ENNReal.ofReal (∫ x, (F i x) ^ p ∂μ)) ^ (2 / p) =
          ENNReal.ofReal (∑ i, (∫ x, (F i x) ^ p ∂μ) ^ (2 / p)) := by
        rw [Finset.sum_congr rfl (fun i _ =>
          ENNReal.ofReal_rpow_of_nonneg (hAi_nn i) (by positivity))]
        exact (ENNReal.ofReal_sum_of_nonneg
          (fun i _ => Real.rpow_nonneg (hAi_nn i) _)).symm
      have hAconv : (ENNReal.ofReal (∫ x, G x ∂μ)) ^ ((p - 2) / p) =
          ENNReal.ofReal ((∫ x, G x ∂μ) ^ ((p - 2) / p)) :=
        ENNReal.ofReal_rpow_of_nonneg hA_nn (by positivity)
      rw [hAconv, hsumconv, ← ENNReal.ofReal_mul (Real.rpow_nonneg hA_nn _)] at hchain
      exact (ENNReal.ofReal_le_ofReal_iff
        (mul_nonneg (Real.rpow_nonneg hA_nn _) hB_nn)).mp hchain
    exact rpow_le_sqrt_of_le_rpow_mul_real hp hA_nn hB_nn hReal

end Commons.Analysis.Integral