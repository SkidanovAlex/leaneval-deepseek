import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.EllExist.Honesty.RadGreenDefs
import Submission.Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

-- Measurability on the far field of the `z^{s⁺}` Green term `G2 α m c` (`s⁺ = 2m/α`):
-- `G2 α m c z = z ^ (2*(m:ℝ)/α) * ∫ t in Set.Ioi z, c t * t ^ (-(2*(m:ℝ)/α) - 1)`.
-- Route: put `g t := c t * t ^ (-(2*(m:ℝ)/α) - 1)`.  `g` is continuous on `Set.Ioi (1/2)` (as
-- `c` is, and `t ↦ t ^ q` is continuous at every `t ≠ 0`) and integrable on `Set.Ioi (1/2)`
-- (`(1/2, 1]` is compact, and on `Set.Ioi 1` the function is dominated by the integrable
-- `t ↦ M * t ^ (-2*(2*(m:ℝ)/α) - 3)` by `hdec`), so
-- `Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi` (base point `1/2`) gives that
-- `u ↦ ∫ t in Set.Ioi u, g t` is differentiable, hence continuous, on `Set.Ioi 1`; multiply by
-- the smooth `z ↦ z ^ (2*(m:ℝ)/α)` for differentiability of `G2`, then `ContinuousOn` gives
-- `MeasureTheory.AEStronglyMeasurable` (`MeasurableSet` `Set.Ioi 1`).
theorem G2_far_measurable (α : ℝ) (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} (M : ℝ)
    (hc : ContinuousOn c (Set.Ioi 0))
    (hdec : ∀ t, 1 ≤ t → |c t| ≤ M * t ^ (-(2 * (m : ℝ) / α) - 2)) :
    MeasureTheory.AEStronglyMeasurable (fun z => Work.FTS.EllExist.Honesty.G2 α m c z)
      (MeasureTheory.volume.restrict (Set.Ioi 1)) := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hq0 : 0 ≤ 2 * (m : ℝ) / α := div_nonneg (by linarith) hα.le
  -- the exponent `-2·s⁺ - 3` of the dominating function is `< -1`
  have hexp : -(2 * (2 * (m : ℝ) / α)) - 3 < -1 := by linarith
  -- `g` is continuous on `Set.Ioi 1`
  have hgcont : ContinuousOn (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1) := by
    have hc1 : ContinuousOn c (Set.Ioi 1) :=
      hc.mono (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
    have hpow : ContinuousOn (fun t : ℝ => t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1) := by
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one (Set.mem_Ioi.mp ht)
      exact (Real.continuousAt_rpow_const t _ <|
        Or.inl (ne_of_gt ht0)).continuousWithinAt
    exact hc1.mul hpow
  have hgaesm : MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (MeasureTheory.volume.restrict (Set.Ioi 1)) :=
    hgcont.aestronglyMeasurable measurableSet_Ioi
  -- the dominating function `t ↦ M·t ^ (-2·s⁺ - 3)` is integrable on `Set.Ioi 1`
  have hdom : MeasureTheory.IntegrableOn
      (fun t : ℝ => M * t ^ (-(2 * (2 * (m : ℝ) / α)) - 3)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hexp zero_lt_one).const_mul M
  -- hence `g` is integrable on `Set.Ioi 1`
  have hgint : MeasureTheory.IntegrableOn
      (fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1) := by
    refine hdom.mono' hgaesm ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) ≤ t := le_of_lt (Set.mem_Ioi.mp ht)
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
    have hp1 : 0 < t ^ (-(2 * (m : ℝ) / α) - 1) := Real.rpow_pos_of_pos ht0 _
    have hlt : |c t| ≤ M * t ^ (-(2 * (m : ℝ) / α) - 2) := hdec t ht1
    have hstep : |c t| * t ^ (-(2 * (m : ℝ) / α) - 1)
        ≤ (M * t ^ (-(2 * (m : ℝ) / α) - 2)) * t ^ (-(2 * (m : ℝ) / α) - 1) :=
      mul_le_mul_of_nonneg_right hlt hp1.le
    have hab : -(2 * (m : ℝ) / α) - 2 + (-(2 * (m : ℝ) / α) - 1)
        = -(2 * (2 * (m : ℝ) / α)) - 3 := by ring
    have hpow : (M * t ^ (-(2 * (m : ℝ) / α) - 2)) * t ^ (-(2 * (m : ℝ) / α) - 1)
        = M * t ^ (-(2 * (2 * (m : ℝ) / α)) - 3) := by
      rw [mul_assoc, ← Real.rpow_add ht0, hab]
    calc ‖c t * t ^ (-(2 * (m : ℝ) / α) - 1)‖
        = |c t| * t ^ (-(2 * (m : ℝ) / α) - 1) := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp1]
      _ ≤ M * t ^ (-(2 * (2 * (m : ℝ) / α)) - 3) := hstep.trans (le_of_eq hpow)
  -- `z ↦ ∫ t in Set.Ioi z, g t` is differentiable, hence continuous, on `Set.Ioi 1`
  have hB : ContinuousOn (fun z : ℝ => ∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1) := by
    intro z hz
    exact (Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi (a := (1 : ℝ))
      (f := fun t : ℝ => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.mem_Ioi.mp hz) hgcont hgint
        ).differentiableAt.continuousAt.continuousWithinAt
  have hzp : ContinuousOn (fun z : ℝ => z ^ (2 * (m : ℝ) / α)) (Set.Ioi 1) := by
    intro z hz
    have hz0 : (0 : ℝ) < z := lt_trans zero_lt_one (Set.mem_Ioi.mp hz)
    exact (Real.continuousAt_rpow_const z _ <|
      Or.inl (ne_of_gt hz0)).continuousWithinAt
  have hcont : ContinuousOn (fun z : ℝ => z ^ (2 * (m : ℝ) / α) *
      ∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1) := hzp.mul hB
  have hG2 : (fun z : ℝ => Work.FTS.EllExist.Honesty.G2 α m c z)
      = fun z : ℝ => z ^ (2 * (m : ℝ) / α) *
          ∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1) := rfl
  rw [hG2]
  exact hcont.aestronglyMeasurable measurableSet_Ioi

end Work.FTS.EllExist.Honesty
