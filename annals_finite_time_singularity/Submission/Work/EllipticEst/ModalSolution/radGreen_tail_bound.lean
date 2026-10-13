import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open MeasureTheory Set

namespace Work.EllipticEst.ModalSolution

theorem radGreen_tail_bound (c : ℝ → ℝ)
    (hc : MeasureTheory.IntegrableOn (fun t => c t ^ 2) (Set.Ioi 0))
    {p z : ℝ} (hp : 0 < p) (hz : 0 < z) :
    |z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))| ≤
      Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1) := by
  have hz0 : 0 ≤ z := le_of_lt hz
  have h2p1 : 0 < 2 * p + 1 := by linarith
  have hsub : Set.Ioi z ⊆ Set.Ioi (0 : ℝ) := Set.Ioi_subset_Ioi hz0
  -- ## the factor `u t = |c t| = √(c t ^ 2)`
  have hu_ae : AEStronglyMeasurable (fun t => Real.sqrt (c t ^ 2)) (volume.restrict (Set.Ioi 0)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hc.1
  have hu_m : AEStronglyMeasurable (fun t => Real.sqrt (c t ^ 2)) (volume.restrict (Set.Ioi z)) :=
    hu_ae.mono_set hsub
  have hu_int : Integrable (fun t => (Real.sqrt (c t ^ 2)) ^ 2) (volume.restrict (Set.Ioi z)) := by
    refine (hc.mono_set hsub).congr (Filter.Eventually.of_forall (fun t => ?_))
    exact (Real.sq_sqrt (sq_nonneg (c t))).symm
  have hu : MemLp (fun t => Real.sqrt (c t ^ 2)) 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hu_m).mpr hu_int
  -- ## the weight `v t = t ^ (-p-1)`
  have hcont_v : ContinuousOn (fun t : ℝ => t ^ (-p - 1)) (Set.Ioi z) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_trans hz ht)))
  have hv_m : AEStronglyMeasurable (fun t : ℝ => t ^ (-p - 1)) (volume.restrict (Set.Ioi z)) :=
    hcont_v.aestronglyMeasurable measurableSet_Ioi
  have hptv : ∀ t : ℝ, 0 < t → t ^ (-2 * p - 2) = (t ^ (-p - 1)) ^ 2 := by
    intro t ht
    rw [pow_two, ← Real.rpow_add ht]
    congr 1
    ring
  have hv_int : Integrable (fun t => (t ^ (-p - 1)) ^ 2) (volume.restrict (Set.Ioi z)) := by
    refine (integrableOn_Ioi_rpow_of_lt (a := -2 * p - 2) (by linarith) hz).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hptv t (lt_trans hz ht)
  have hv : MemLp (fun t => t ^ (-p - 1)) 2 (volume.restrict (Set.Ioi z)) :=
    (memLp_two_iff_integrable_sq hv_m).mpr hv_int
  -- ## the value of `∫_z^∞ t ^ (-2p-2)`
  have hVval : (∫ t in Set.Ioi z, t ^ (-2 * p - 2)) = z ^ (-2 * p - 1) / (2 * p + 1) := by
    have h := integral_Ioi_rpow_of_lt (a := -2 * p - 2) (c := z) (by linarith) hz
    have h' : -z ^ ((-2 * p - 2 : ℝ) + 1) / ((-2 * p - 2 : ℝ) + 1)
        = z ^ (-2 * p - 1) / (2 * p + 1) := by
      rw [show ((-2 * p - 2 : ℝ) + 1) = -(2 * p + 1) by ring]
      rw [neg_div_neg_eq]
      rw [show -(2 * p + 1 : ℝ) = -2 * p - 1 by ring]
    rw [h, h']
  have hIntV : (∫ t in Set.Ioi z, (t ^ (-p - 1)) ^ 2) = z ^ (-2 * p - 1) / (2 * p + 1) := by
    rw [show (∫ t in Set.Ioi z, (t ^ (-p - 1)) ^ 2) = ∫ t in Set.Ioi z, t ^ (-2 * p - 2) from
      integral_congr_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact (hptv t (lt_trans hz ht)).symm)]
    exact hVval
  have hIntU : (∫ t in Set.Ioi z, (Real.sqrt (c t ^ 2)) ^ 2) = ∫ t in Set.Ioi z, c t ^ 2 :=
    integral_congr_ae (Filter.Eventually.of_forall (fun t => Real.sq_sqrt (sq_nonneg (c t))))
  -- ## Cauchy–Schwarz
  have hCS := Work.FTS.EllipticEst.remov.Ebs.abs_integral_mul_le_sqrt hu hv
  have hCS' : (∫ t in Set.Ioi z, Real.sqrt (c t ^ 2) * t ^ (-p - 1)) ≤
      Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) * Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1)) := by
    refine le_trans (le_abs_self _) (le_trans hCS ?_)
    rw [hIntU, hIntV]
  -- ## the tail integral itself, bounded by the `L²` pairing
  have hJ : |∫ t in Set.Ioi z, c t * t ^ (-p - 1)| ≤
      ∫ t in Set.Ioi z, Real.sqrt (c t ^ 2) * t ^ (-p - 1) := by
    have h1 : |∫ t in Set.Ioi z, c t * t ^ (-p - 1)| ≤
        ∫ t in Set.Ioi z, ‖c t * t ^ (-p - 1)‖ := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi z))
          (f := fun t => c t * t ^ (-p - 1)))
    refine le_trans h1 (le_of_eq ?_)
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hz ht
    rw [Real.norm_eq_abs, abs_mul, Real.sqrt_sq_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos ht0 (-p - 1))]
  have hmain : |∫ t in Set.Ioi z, c t * t ^ (-p - 1)| ≤
      Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) * Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1)) :=
    le_trans hJ hCS'
  -- ## monotonicity of the `L²` mass in the domain
  have hUQ : (∫ t in Set.Ioi z, c t ^ 2) ≤ ∫ t in Set.Ioi 0, c t ^ 2 := by
    refine setIntegral_mono_set (μ := volume) (s := Set.Ioi z) (t := Set.Ioi 0) hc ?_ ?_
    · exact Filter.Eventually.of_forall (fun t => sq_nonneg (c t))
    · exact Filter.Eventually.of_forall (fun t ht => lt_trans hz ht)
  have hsqrtUQ : Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) :=
    Real.sqrt_le_sqrt hUQ
  -- ## the weight computation
  have hW : z ^ p * Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1)) =
      z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1) := by
    have hzW : 0 ≤ z ^ (-2 * p - 1) := le_of_lt (Real.rpow_pos_of_pos hz _)
    have hsq : Real.sqrt (z ^ (-2 * p - 1)) = z ^ (-p - (1 / 2)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz0]
      rw [show (-2 * p - 1) * (1 / 2) = -p - (1 / 2) by ring]
    rw [Real.sqrt_div hzW (2 * p + 1), hsq]
    rw [← mul_div_assoc, ← Real.rpow_add hz]
    rw [show p + (-p - (1 / 2)) = -(1 / 2 : ℝ) by ring]
  have hzp : 0 < z ^ p := Real.rpow_pos_of_pos hz p
  calc |z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))|
      = z ^ p * |∫ t in Set.Ioi z, c t * t ^ (-p - 1)| := by
        rw [abs_mul, abs_of_pos hzp]
    _ ≤ z ^ p * (Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) *
          Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1))) :=
        mul_le_mul_of_nonneg_left hmain (le_of_lt hzp)
    _ = Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) *
          (z ^ p * Real.sqrt (z ^ (-2 * p - 1) / (2 * p + 1))) := by ring
    _ = Real.sqrt (∫ t in Set.Ioi z, c t ^ 2) *
          (z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1)) := by rw [hW]
    _ ≤ Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) *
          (z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1)) :=
        mul_le_mul_of_nonneg_right hsqrtUQ
          (div_nonneg (le_of_lt (Real.rpow_pos_of_pos hz _)) (Real.sqrt_nonneg _))
    _ = Real.sqrt (∫ t in Set.Ioi 0, c t ^ 2) * z ^ (-(1 / 2) : ℝ) / Real.sqrt (2 * p + 1) := by
        rw [mul_div_assoc]

end Work.EllipticEst.ModalSolution
