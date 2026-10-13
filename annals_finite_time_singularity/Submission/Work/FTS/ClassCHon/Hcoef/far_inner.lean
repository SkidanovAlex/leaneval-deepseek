import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.ClassCHon.RgL2Pointwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Hcoef

theorem far_inner {p L a b : ℝ} (hp : 0 < p) (ha : 0 < a) (hab : a ≤ b) (hL : 0 ≤ L)
    {c : ℝ → ℝ} (hcm : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioc a b)))
    (hc : ∀ t ∈ Set.Icc a b, |c t| ≤ L) :
    MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-p - 1)) (Set.Ioc a b) ∧
      |∫ t in Set.Ioc a b, c t * t ^ (-p - 1)| ≤ L * a ^ (-p) / p := by
  have hp1 : -p - 1 < -1 := by linarith
  -- the majorant `t ↦ L * t ^ (-p - 1)` is integrable on `Ioc a b`
  have hpow_int : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-p - 1)) (Set.Ioc a b) :=
    (integrableOn_Ioi_rpow_of_lt hp1 ha).mono_set Set.Ioc_subset_Ioi_self
  have hL_int : MeasureTheory.IntegrableOn (fun t : ℝ => L * t ^ (-p - 1)) (Set.Ioc a b) :=
    hpow_int.const_mul L
  -- measurability of the power function on `Ioc a b` (where it is continuous)
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-p - 1)) (Set.Ioc a b) := by
    intro t ht
    exact (Real.continuousAt_rpow_const t (-p - 1)
      (Or.inl (ne_of_gt (ha.trans ht.1)))).continuousWithinAt
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => c t * t ^ (-p - 1))
      (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
    hcm.mul (hcont.aestronglyMeasurable measurableSet_Ioc)
  -- pointwise domination on `Ioc a b`
  have hbound : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioc a b)),
      ‖c t * t ^ (-p - 1)‖ ≤ L * t ^ (-p - 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have htpos : 0 < t := ha.trans ht.1
    have hpownn : 0 ≤ t ^ (-p - 1) := Real.rpow_nonneg htpos.le _
    have hct : |c t| ≤ L := hc t ⟨le_of_lt ht.1, ht.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpownn]
    exact mul_le_mul_of_nonneg_right hct hpownn
  have hintc : MeasureTheory.IntegrableOn (fun t : ℝ => c t * t ^ (-p - 1)) (Set.Ioc a b) :=
    MeasureTheory.Integrable.mono' hL_int hmeas hbound
  refine ⟨hintc, ?_⟩
  -- `|∫ f| ≤ ∫ |f| ≤ ∫ L t^{-p-1} ≤ L a^{-p}/p`
  have h1 : |∫ t in Set.Ioc a b, c t * t ^ (-p - 1)|
      ≤ ∫ t in Set.Ioc a b, |c t * t ^ (-p - 1)| := by
    have := MeasureTheory.norm_integral_le_integral_norm
      (μ := MeasureTheory.volume.restrict (Set.Ioc a b)) (fun t : ℝ => c t * t ^ (-p - 1))
    simpa only [Real.norm_eq_abs] using this
  have h2 : ∫ t in Set.Ioc a b, |c t * t ^ (-p - 1)|
      ≤ ∫ t in Set.Ioc a b, L * t ^ (-p - 1) := by
    refine MeasureTheory.setIntegral_mono_on ?_ hL_int measurableSet_Ioc ?_
    · exact hintc.norm
    · intro t ht
      have htpos : 0 < t := ha.trans ht.1
      have hpownn : 0 ≤ t ^ (-p - 1) := Real.rpow_nonneg htpos.le _
      have hct : |c t| ≤ L := hc t ⟨le_of_lt ht.1, ht.2⟩
      rw [abs_mul, abs_of_nonneg hpownn]
      exact mul_le_mul_of_nonneg_right hct hpownn
  have h3 : ∫ t in Set.Ioc a b, L * t ^ (-p - 1) = L * ∫ t in Set.Ioc a b, t ^ (-p - 1) :=
    MeasureTheory.integral_const_mul L (fun t : ℝ => t ^ (-p - 1))
  have h4 : ∫ t in Set.Ioc a b, t ^ (-p - 1) ≤ ∫ t in Set.Ioi a, t ^ (-p - 1) := by
    refine MeasureTheory.setIntegral_mono_set (integrableOn_Ioi_rpow_of_lt hp1 ha) ?_ ?_
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      exact Real.rpow_nonneg (le_trans ha.le (le_of_lt ht)) _
    · exact Filter.Eventually.of_forall (fun t ht => ht.1)
  have h5 : ∫ t in Set.Ioi a, t ^ (-p - 1) = a ^ (-p) / p := by
    rw [integral_Ioi_rpow_of_lt hp1 ha, show -p - 1 + 1 = -p from by ring, neg_div_neg_eq]
  calc |∫ t in Set.Ioc a b, c t * t ^ (-p - 1)|
      ≤ ∫ t in Set.Ioc a b, L * t ^ (-p - 1) := le_trans h1 h2
    _ = L * ∫ t in Set.Ioc a b, t ^ (-p - 1) := h3
    _ ≤ L * (a ^ (-p) / p) := mul_le_mul_of_nonneg_left (le_trans h4 (le_of_eq h5)) hL
    _ = L * a ^ (-p) / p := by ring

end Work.FTS.ClassCHon.Hcoef
