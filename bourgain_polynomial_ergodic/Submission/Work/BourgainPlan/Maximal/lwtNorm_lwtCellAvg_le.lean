import Mathlib
import Submission.Work.BourgainPlan.Maximal.lwtCZDefs
import Submission.Commons.Analysis.MeasureTheory.minkowski_lintegral_sum

open MeasureTheory Set
open scoped ENNReal BigOperators Classical

namespace Work.BourgainPlan.Maximal

/-- The `ENNReal` lift of `lwtNorm`: `ofReal ((Σ_t A_t(y)²)^{1/2})` is
`(Σ_t (ofReal (A_t y))²)^{1/2}`. -/
lemma ofReal_lwtNorm_eq {n : ℕ} {A : Fin n → ℝ → ℝ} (hA : ∀ t y, 0 ≤ A t y) (y : ℝ) :
    ENNReal.ofReal (lwtNorm A y)
      = (∑ t : Fin n, (ENNReal.ofReal (A t y)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  have hsum : (0 : ℝ) ≤ ∑ t : Fin n, (A t y) ^ 2 :=
    Finset.sum_nonneg fun t _ => sq_nonneg _
  have h1 : lwtNorm A y = (∑ t : Fin n, (A t y) ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [lwtNorm, Real.sqrt_eq_rpow]
  rw [h1, ← ENNReal.ofReal_rpow_of_nonneg hsum (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.ofReal_sum_of_nonneg (fun t _ => sq_nonneg _)]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
    ENNReal.ofReal_pow (hA t y)]

/-- **Minkowski's integral inequality for the `ℓ²`-norm of a nonnegative finite family:**
the `ℓ²`-norm of the integrals is bounded by the integral of the `ℓ²`-norms. -/
lemma sqrt_sum_integral_sq_le_integral_lwtNorm {n : ℕ} {A : Fin n → ℝ → ℝ} {s : Set ℝ}
    (hA : ∀ t y, 0 ≤ A t y) (hs : MeasurableSet s)
    (hint : ∀ t, IntegrableOn (A t) s) (hintN : IntegrableOn (lwtNorm A) s) :
    (∑ t : Fin n, (∫ y in s, A t y) ^ 2) ^ ((1 : ℝ) / 2) ≤ ∫ y in s, lwtNorm A y := by
  have hNnn : (0 : ℝ) ≤ ∫ y in s, lwtNorm A y :=
    setIntegral_nonneg hs fun y _ => lwtNorm_nonneg A y
  refine (ENNReal.ofReal_le_ofReal_iff hNnn).mp ?_
  have hFint : ∀ t : Fin n,
      ∫⁻ y in s, ENNReal.ofReal (A t y) = ENNReal.ofReal (∫ y in s, A t y) := by
    intro t
    exact (ofReal_integral_eq_lintegral_ofReal (hint t)
      (Filter.Eventually.of_forall fun y => hA t y)).symm
  have hFmeas : ∀ t : Fin n,
      AEMeasurable (fun y => ENNReal.ofReal (A t y)) (volume.restrict s) :=
    fun t => (hint t).aemeasurable.ennreal_ofReal
  have hmink := Commons.Analysis.MeasureTheory.minkowski_lintegral_sum (μ := volume.restrict s)
    (Finset.univ : Finset (Fin n)) (fun t y => ENNReal.ofReal (A t y)) 2 (by norm_num) hFmeas
  have hpoint : ∀ y : ℝ,
      (∑ t : Fin n, (ENNReal.ofReal (A t y)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        = ENNReal.ofReal (lwtNorm A y) := fun y => (ofReal_lwtNorm_eq hA y).symm
  calc ENNReal.ofReal ((∑ t : Fin n, (∫ y in s, A t y) ^ 2) ^ ((1 : ℝ) / 2))
      = (∑ t : Fin n, (ENNReal.ofReal (∫ y in s, A t y)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
        rw [← ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg fun t _ => sq_nonneg _)
              (by norm_num : (0 : ℝ) ≤ 1 / 2),
            ENNReal.ofReal_sum_of_nonneg (fun t _ => sq_nonneg _)]
        congr 1
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
          ENNReal.ofReal_pow (setIntegral_nonneg hs fun y _ => hA t y)]
    _ = (∑ t : Fin n, (∫⁻ y in s, ENNReal.ofReal (A t y)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
        congr 1
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hFint t]
    _ ≤ ∫⁻ y in s, (∑ t : Fin n, (ENNReal.ofReal (A t y)) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := hmink
    _ = ∫⁻ y in s, ENNReal.ofReal (lwtNorm A y) := lintegral_congr hpoint
    _ = ENNReal.ofReal (∫ y in s, lwtNorm A y) :=
        (ofReal_integral_eq_lintegral_ofReal hintN
          (Filter.Eventually.of_forall fun y => lwtNorm_nonneg A y)).symm

theorem lwtNorm_lwtCellAvg_le {n : ℕ} {A : Fin n → ℝ → ℝ} (hA : ∀ t y, 0 ≤ A t y)
    (hint : ∀ t, MeasureTheory.Integrable (A t))
    (hintN : MeasureTheory.Integrable (Work.BourgainPlan.Maximal.lwtNorm A)) (p : ℤ × ℤ) :
    (Finset.sum Finset.univ (fun t : Fin n => (Work.BourgainPlan.Maximal.lwtCellAvg (A t) p) ^ 2))
        ^ ((1 : ℝ) / 2)
      ≤ Work.BourgainPlan.Maximal.lwtCellAvg (Work.BourgainPlan.Maximal.lwtNorm A) p := by
  have hcore := sqrt_sum_integral_sq_le_integral_lwtNorm (s := dyCell p.1 p.2) hA
    (dyCell_measurable p.1 p.2) (fun t => (hint t).integrableOn) hintN.integrableOn
  have hw : (0 : ℝ) < ((2 : ℝ) ^ p.1)⁻¹ := inv_pos.mpr (zpow_two_pos p.1)
  have hroot : (∑ t : Fin n,
        (((2 : ℝ) ^ p.1)⁻¹ * ∫ y in dyCell p.1 p.2, A t y) ^ 2) ^ ((1 : ℝ) / 2)
      = ((2 : ℝ) ^ p.1)⁻¹ * (∑ t : Fin n, (∫ y in dyCell p.1 p.2, A t y) ^ 2) ^ ((1 : ℝ) / 2) := by
    have hsq : (∑ t : Fin n, (((2 : ℝ) ^ p.1)⁻¹ * ∫ y in dyCell p.1 p.2, A t y) ^ 2)
        = ((2 : ℝ) ^ p.1)⁻¹ ^ 2 * ∑ t : Fin n, (∫ y in dyCell p.1 p.2, A t y) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, hsq,
      Real.sqrt_mul (sq_nonneg ((2 : ℝ) ^ p.1)⁻¹),
      Real.sqrt_sq_eq_abs, abs_of_pos hw]
  have key : (∑ t : Fin n, (lwtCellAvg (A t) p) ^ 2) ^ ((1 : ℝ) / 2)
      = ((2 : ℝ) ^ p.1)⁻¹ * (∑ t : Fin n, (∫ y in dyCell p.1 p.2, A t y) ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [Finset.sum_congr rfl (fun t _ => by rw [lwtCellAvg])]
    exact hroot
  rw [key, lwtCellAvg]
  exact mul_le_mul_of_nonneg_left hcore hw.le

end Work.BourgainPlan.Maximal
