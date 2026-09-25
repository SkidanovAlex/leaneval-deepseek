import Mathlib
import Submission.Work.BourgainPlan.Oscillation.Lacunary.dilProfDefs

namespace Work.BourgainPlan.Oscillation.Lacunary

open Finset MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- Interval integrability on `(0,1]` from a bound valid only there. -/
private lemma profFam_intervalIntegrable_of_Ioc_bound {h : ℝ → ℂ} (hh : Measurable h) {C : ℝ}
    (hC : ∀ θ ∈ Set.Ioc (0:ℝ) 1, ‖h θ‖ ≤ C) : IntervalIntegrable h volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hfin : volume (Set.Ioc (0:ℝ) 1) < ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  exact IntegrableOn.of_bound hfin hh.aestronglyMeasurable C
    (ae_restrict_of_forall_mem measurableSet_Ioc hC)

theorem profFam_add_eq (ρ : ℝ) (r : ℝ → ℂ) (hr : Measurable r) (cap : ℝ) (hcap : 0 ≤ cap)
    (hrb : ∀ θ, ‖r θ‖ ≤ cap) (H H₁ H₂ : ℝ → ℂ) (hH : ∀ u, H u = H₁ u + H₂ u)
    (hH₁m : Measurable H₁) (hH₂m : Measurable H₂) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hH₁b : ∀ u, 0 < u → ‖H₁ u‖ ≤ M) (hH₂b : ∀ u, 0 < u → ‖H₂ u‖ ≤ A)
    (f : ℤ → ℂ) (T : Finset ℤ) (i : ℕ) (x : ℤ) :
    Work.BourgainPlan.Oscillation.Lacunary.profFam H r f T ρ i x
      = Work.BourgainPlan.Oscillation.Lacunary.profFam H₁ r f T ρ i x
        + Work.BourgainPlan.Oscillation.Lacunary.profFam H₂ r f T ρ i x := by
  have hm1 : Measurable (fun θ : ℝ =>
      (r θ * H₁ ((lacScale ρ i : ℝ) * θ)) * trigP T f θ * Echar x θ) :=
    ((hr.mul (hH₁m.comp (measurable_const.mul measurable_id))).mul (measurable_trigP T f)).mul
      (continuous_Echar x).measurable
  have hm2 : Measurable (fun θ : ℝ =>
      (r θ * H₂ ((lacScale ρ i : ℝ) * θ)) * trigP T f θ * Echar x θ) :=
    ((hr.mul (hH₂m.comp (measurable_const.mul measurable_id))).mul (measurable_trigP T f)).mul
      (continuous_Echar x).measurable
  have hint1 : IntervalIntegrable
      (fun θ : ℝ => (r θ * H₁ ((lacScale ρ i : ℝ) * θ)) * trigP T f θ * Echar x θ) volume 0 1 := by
    have hc0 : (0:ℝ) ≤ (lacScale ρ i : ℝ) := by positivity
    rcases eq_or_lt_of_le hc0 with hc | hc
    · refine profFam_intervalIntegrable_of_Ioc_bound hm1
        (C := cap * ‖H₁ 0‖ * (∑ j ∈ T, ‖f j‖)) ?_
      intro θ hθ
      have hzero : (lacScale ρ i : ℝ) * θ = 0 := by rw [← hc]; ring
      rw [hzero, norm_mul, norm_mul, norm_mul, norm_Echar, mul_one]
      refine mul_le_mul (mul_le_mul (hrb θ) le_rfl (norm_nonneg _) hcap)
        (norm_trigP_le T f θ) (norm_nonneg _)
        (mul_nonneg hcap (norm_nonneg _))
    · refine profFam_intervalIntegrable_of_Ioc_bound hm1
        (C := cap * M * (∑ j ∈ T, ‖f j‖)) ?_
      intro θ hθ
      have hpos : 0 < (lacScale ρ i : ℝ) * θ := mul_pos hc hθ.1
      rw [norm_mul, norm_mul, norm_mul, norm_Echar, mul_one]
      refine mul_le_mul (mul_le_mul (hrb θ) (hH₁b _ hpos) (norm_nonneg _) hcap)
        (norm_trigP_le T f θ) (norm_nonneg _)
        (mul_nonneg hcap hM)
  have hint2 : IntervalIntegrable
      (fun θ : ℝ => (r θ * H₂ ((lacScale ρ i : ℝ) * θ)) * trigP T f θ * Echar x θ) volume 0 1 := by
    have hc0 : (0:ℝ) ≤ (lacScale ρ i : ℝ) := by positivity
    rcases eq_or_lt_of_le hc0 with hc | hc
    · refine profFam_intervalIntegrable_of_Ioc_bound hm2
        (C := cap * ‖H₂ 0‖ * (∑ j ∈ T, ‖f j‖)) ?_
      intro θ hθ
      have hzero : (lacScale ρ i : ℝ) * θ = 0 := by rw [← hc]; ring
      rw [hzero, norm_mul, norm_mul, norm_mul, norm_Echar, mul_one]
      refine mul_le_mul (mul_le_mul (hrb θ) le_rfl (norm_nonneg _) hcap)
        (norm_trigP_le T f θ) (norm_nonneg _)
        (mul_nonneg hcap (norm_nonneg _))
    · refine profFam_intervalIntegrable_of_Ioc_bound hm2
        (C := cap * A * (∑ j ∈ T, ‖f j‖)) ?_
      intro θ hθ
      have hpos : 0 < (lacScale ρ i : ℝ) * θ := mul_pos hc hθ.1
      rw [norm_mul, norm_mul, norm_mul, norm_Echar, mul_one]
      refine mul_le_mul (mul_le_mul (hrb θ) (hH₂b _ hpos) (norm_nonneg _) hcap)
        (norm_trigP_le T f θ) (norm_nonneg _)
        (mul_nonneg hcap hA)
  rw [profFam_def, profFam_def, profFam_def]
  rw [show (∫ θ in (0:ℝ)..1, (r θ * H ((lacScale ρ i : ℝ) * θ)) * trigP T f θ * Echar x θ)
      = ∫ θ in (0:ℝ)..1, ((r θ * H₁ ((lacScale ρ i : ℝ) * θ)) * trigP T f θ * Echar x θ)
          + ((r θ * H₂ ((lacScale ρ i : ℝ) * θ)) * trigP T f θ * Echar x θ) from
      intervalIntegral.integral_congr (fun θ _ => by simp only [hH]; ring)]
  rw [intervalIntegral.integral_add hint1 hint2]

end

end Work.BourgainPlan.Oscillation.Lacunary
