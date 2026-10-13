import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open MeasureTheory Set

/-- Pointwise AM–GM bound behind the tail estimate: for `t > 0`,
`‖φ t‖ ≤ (1/2) * ((t * φ t)² * t^{-1/2}) + (1/2) * t^{-3/2}`. -/
private lemma tail_pointwise_bound (φ : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    ‖φ t‖ ≤ (1/2) * ((t * φ t)^2 * t^(-(1/2:ℝ))) + (1/2) * t^(-(3/2:ℝ)) := by
  rw [Real.norm_eq_abs]
  set A : ℝ := |t * φ t| * t^(-(1/4:ℝ)) with hA
  set B : ℝ := t^(-(3/4:ℝ)) with hB
  have hAB : A * B = |φ t| := by
    rw [hA, hB, mul_assoc, ← Real.rpow_add ht]
    have he : (-(1/4:ℝ)) + (-(3/4:ℝ)) = -1 := by norm_num
    rw [he, Real.rpow_neg_one, abs_mul, abs_of_pos ht]
    field_simp
  have hAA : A^2 = (t * φ t)^2 * t^(-(1/2:ℝ)) := by
    rw [hA, mul_pow]
    have hpow : (t^(-(1/4:ℝ)))^2 = t^(-(1/2:ℝ)) := by
      rw [pow_two, ← Real.rpow_add ht]; norm_num
    have habs : |t * φ t|^2 = (t * φ t)^2 := sq_abs _
    rw [habs, hpow]
  have hBB : B^2 = t^(-(3/2:ℝ)) := by
    rw [hB, pow_two, ← Real.rpow_add ht]; norm_num
  have key : 2 * (A * B) ≤ A^2 + B^2 := by nlinarith [sq_nonneg (A - B)]
  have h2 : 2 * |φ t| ≤ (t * φ t)^2 * t^(-(1/2:ℝ)) + t^(-(3/2:ℝ)) := by
    rw [← hAB, ← hAA, ← hBB]
    exact key
  linarith

theorem integrableOn_tail_of_weighted (z : ℝ) (hz : 0 < z) (φ : ℝ → ℝ)
    (hφmeas : MeasureTheory.AEStronglyMeasurable φ (MeasureTheory.volume.restrict (Set.Ioi z)))
    (hφG : MeasureTheory.IntegrableOn (fun t : ℝ => (t * φ t) ^ 2 * t ^ (-(1/2:ℝ))) (Set.Ioi z)) :
    MeasureTheory.IntegrableOn φ (Set.Ioi z) := by
  -- `IntegrableOn f s μ` is `Integrable f (μ.restrict s)` by definition.
  have hsmall : Integrable (fun t : ℝ => t^(-(3/2:ℝ))) (volume.restrict (Ioi z)) :=
    integrableOn_Ioi_rpow_of_lt (a := -(3/2:ℝ)) (by norm_num) hz
  have hdom : Integrable
      (fun t : ℝ => (1/2) * ((t * φ t)^2 * t^(-(1/2:ℝ))) + (1/2) * t^(-(3/2:ℝ)))
      (volume.restrict (Ioi z)) :=
    (hφG.const_mul (1/2)).add (hsmall.const_mul (1/2))
  refine Integrable.mono' hdom hφmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  exact tail_pointwise_bound φ (lt_trans hz ht)

end Work.Elliptic
