import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.PhiStar.Radial.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.RadGreenSupport

/-- From the hypothesis `|c^(k)(t)| ≤ A/(1+t^{k+1})` at `k = 0` one gets the two elementary
bounds on `|c|` used below: `|c t| ≤ A/(1+t)` and `|c t| ≤ A` for `t > 0`. -/
theorem src_abs_le {A : ℝ} (hA : 0 ≤ A) {c : ℝ → ℝ}
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ t : ℝ, 0 < t → |iteratedDeriv k c t| ≤ A / (1 + t ^ (k + 1))) :
    (∀ t : ℝ, 0 < t → |c t| ≤ A / (1 + t)) ∧ (∀ t : ℝ, 0 < t → |c t| ≤ A) := by
  have hc_le : ∀ t : ℝ, 0 < t → |c t| ≤ A / (1 + t) := by
    intro t ht
    have h := hb 0 (by norm_num : (0 : ℕ) ≤ 2) t ht
    simpa only [iteratedDeriv_zero, Nat.zero_add, pow_one] using h
  refine ⟨hc_le, fun t ht => ?_⟩
  refine le_trans (hc_le t ht) ?_
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + t)]
  nlinarith [hA, ht]

theorem src_integrable {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hc : ContDiffOn ℝ 2 c (Set.Ioi 0))
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ t : ℝ, 0 < t → |iteratedDeriv k c t| ≤ A / (1 + t ^ (k + 1))) :
    MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1) ∧
    MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1) := by
  obtain ⟨hc_le, hc_le_A⟩ := src_abs_le hA hb
  have hm0 : (0 : ℝ) ≤ 2 * (m : ℝ) / α := by
    apply div_nonneg
    · have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    · exact hα.le
  have hnum : (0 : ℝ) < 2 * (m : ℝ) + 5 := by
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  constructor
  · -- on `(0,1)`: dominate by `A * t^(p-1)` with `p - 1 > -1`
    rw [MeasureTheory.IntegrableOn]
    refine MeasureTheory.Integrable.mono'
      (g := fun t : ℝ => A * t ^ ((2 * (m : ℝ) + 5) / α - 1)) ?_ ?_ ?_
    · have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ ((2 * (m : ℝ) + 5) / α - 1))
          (Set.Ioo (0 : ℝ) 1) :=
        (intervalIntegral.integrableOn_Ioo_rpow_iff (show (0 : ℝ) < 1 by norm_num)).2
          (by have := div_pos hnum hα; linarith)
      exact MeasureTheory.Integrable.const_mul hbase A
    · have hcont : ContinuousOn (fun t : ℝ => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
          (Set.Ioo (0 : ℝ) 1) :=
        (hc.continuousOn.mono Set.Ioo_subset_Ioi_self).mul
          (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx.1)))
      exact hcont.aestronglyMeasurable measurableSet_Ioo
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
      exact mul_le_mul_of_nonneg_right (hc_le_A t ht.1) (Real.rpow_nonneg ht.1.le _)
  · -- on `(1,∞)`: use `|c t| ≤ A/t`, leaving the exponent `-2m/α - 2 < -1`
    rw [MeasureTheory.IntegrableOn]
    refine MeasureTheory.Integrable.mono'
      (g := fun t : ℝ => A * t ^ (-(2 * (m : ℝ) / α) - 2)) ?_ ?_ ?_
    · have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-(2 * (m : ℝ) / α) - 2))
          (Set.Ioi 1) :=
        (integrableOn_Ioi_rpow_iff (show (0 : ℝ) < 1 by norm_num)).2 (by linarith)
      exact MeasureTheory.Integrable.const_mul hbase A
    · have hcont : ContinuousOn (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
          (Set.Ioi 1) :=
        (hc.continuousOn.mono (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).mul
          (continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (lt_trans zero_lt_one hx))))
      exact hcont.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
      have hct : |c t| ≤ A / t :=
        le_trans (hc_le t ht0) (div_le_div_of_nonneg_left hA ht0 (by linarith))
      have h1 : t ^ (-1 : ℝ) * t ^ (-(2 * (m : ℝ) / α) - 1)
          = t ^ (-(2 * (m : ℝ) / α) - 2) := by
        have hexp : -1 + (-(2 * (m : ℝ) / α) - 1) = -(2 * (m : ℝ) / α) - 2 := by ring
        rw [← Real.rpow_add ht0, hexp]
      calc |c t| * t ^ (-(2 * (m : ℝ) / α) - 1)
          ≤ (A / t) * t ^ (-(2 * (m : ℝ) / α) - 1) :=
            mul_le_mul_of_nonneg_right hct (Real.rpow_nonneg ht0.le _)
        _ = A * (t ^ (-1 : ℝ) * t ^ (-(2 * (m : ℝ) / α) - 1)) := by
              rw [div_eq_mul_inv, ← Real.rpow_neg_one t]
              ring
        _ = A * t ^ (-(2 * (m : ℝ) / α) - 2) := by rw [h1]

end Work.FTS.PhiStar.RadGreenSupport
