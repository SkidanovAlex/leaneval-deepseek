import Mathlib
import Submission.Work.CR.Flat.Cauchy

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

/-- Polar-coordinate evaluation of `∫_{‖w‖<ρ} ‖w‖^s` for `-2 < s` and `0 < ρ`:
writing `w = r (cos θ + i sin θ)` gives `∫₀^ρ ∫_{-π}^{π} r * r^s dθ dr
= 2 π ρ^{s+2}/(s+2)`.  This is the elementary estimate behind the bound for the
Cauchy potential. -/
lemma norm_cauchyTransform_le_aux_disc {ρ s : ℝ} (hρ : 0 < ρ) (hs : -2 < s) :
    ∫ w in Metric.ball (0 : ℂ) ρ, ‖w‖ ^ s = 2 * Real.pi * ρ ^ (s + 2) / (s + 2) := by
  have hangle : (∫ y in Set.Ioo (-Real.pi) Real.pi, (1:ℝ)) = 2 * Real.pi := by
    rw [MeasureTheory.integral_const, smul_eq_mul, mul_one]
    rw [MeasureTheory.Measure.real, MeasureTheory.Measure.restrict_apply MeasurableSet.univ]
    simp only [Set.univ_inter]
    rw [Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hrad : (∫ x in Set.Ioi (0:ℝ), x * (if |x| < ρ then |x| ^ s else 0))
      = ρ ^ (s + 2) / (s + 2) := by
    have h1 : (∫ x in Set.Ioi (0:ℝ), x * (if |x| < ρ then |x| ^ s else 0))
        = ∫ x in Set.Ioi (0:ℝ), (Set.Iio ρ).indicator (fun x => x ^ (s + 1)) x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx' : 0 < x := hx
      show x * (if |x| < ρ then |x| ^ s else 0) = _
      rw [abs_of_pos hx']
      simp only [Set.indicator, Set.mem_Iio]
      by_cases h : x < ρ
      · rw [if_pos h, if_pos h, Real.rpow_add hx', Real.rpow_one]; ring
      · rw [if_neg h, if_neg h, mul_zero]
    rw [h1, setIntegral_indicator measurableSet_Iio]
    rw [show Set.Ioi (0:ℝ) ∩ Set.Iio ρ = Set.Ioo (0:ℝ) ρ from rfl]
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hρ.le]
    rw [integral_rpow (Or.inl (by linarith : (-1:ℝ) < s + 1))]
    rw [Real.zero_rpow (by linarith : s + 1 + 1 ≠ 0)]
    ring_nf
  rw [← integral_indicator (Metric.isOpen_ball.measurableSet)]
  rw [← Complex.integral_comp_polarCoord_symm
      (fun w => (Metric.ball (0:ℂ) ρ).indicator (fun w => ‖w‖ ^ s) w)]
  rw [show (polarCoord.target : Set (ℝ × ℝ))
      = Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi from rfl]
  simp only [Set.indicator, Metric.mem_ball, dist_zero_right, smul_eq_mul,
    Complex.norm_polarCoord_symm]
  rw [show (∫ p in Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        p.1 * (if |p.1| < ρ then |p.1| ^ s else 0))
      = (∫ x in Set.Ioi (0:ℝ), x * (if |x| < ρ then |x| ^ s else 0))
          * (∫ y in Set.Ioo (-Real.pi) Real.pi, (1:ℝ)) from by
    rw [← setIntegral_prod_mul, MeasureTheory.Measure.volume_eq_prod]
    simp_rw [mul_one]]
  rw [hangle, hrad]
  ring

/-- Pointwise bound for the Cauchy potential `cauchyTransform ρ f z =
-(1/π) ∫_{‖w‖<ρ} (f (z+w) - f z)/w` of `Submission/Work/CR/Flat/Cauchy.lean`.

If `f` is `α`-Hölder with constant `C` (`0 < α`) then
`‖T f z‖ ≤ C ∫_{‖w‖<ρ} ‖w‖^{α-1} = 2 C ρ^{α+1}/(α+1)`.
The subtraction in the kernel is what makes the integral absolutely convergent;
no support condition on `f` is needed. -/
theorem norm_cauchyTransform_le {ρ α C : ℝ} (hα : 0 < α) (hC : 0 ≤ C) {f : ℂ → ℂ}
    (hf : ∀ x y : ℂ, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) {z : ℂ} (hz : ‖z‖ < ρ) :
    ‖cauchyTransform ρ f z‖ ≤ 2 * C * ρ ^ (α + 1) / (α + 1) := by
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg z) hz
  -- pointwise bound on the integrand
  have hpt : ∀ w : ℂ, ‖(f (z + w) - f z) / w‖ ≤ C * ‖w‖ ^ (α - 1) := by
    intro w
    by_cases hw : w = 0
    · subst hw
      simp only [add_zero, sub_self, norm_zero, zero_div]
      by_cases h : α - 1 = 0
      · rw [h, Real.rpow_zero]; simpa using hC
      · rw [Real.zero_rpow h]; simp
    · rw [norm_div]
      have hfw : ‖f (z + w) - f z‖ ≤ C * ‖w‖ ^ α := by
        have h := hf (z + w) z
        rwa [add_sub_cancel_left] at h
      calc ‖f (z + w) - f z‖ / ‖w‖ ≤ C * ‖w‖ ^ α / ‖w‖ :=
            div_le_div_of_nonneg_right hfw (norm_nonneg w)
        _ = C * ‖w‖ ^ (α - 1) := by
            have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
            rw [Real.rpow_sub hw', Real.rpow_one]
            ring
  -- integrability of the majorant on the disc
  have hmeas : AEStronglyMeasurable (fun w : ℂ => C * ‖w‖ ^ (α - 1)) volume :=
    (by measurability : Measurable (fun w : ℂ => C * ‖w‖ ^ (α - 1))).aestronglyMeasurable
  have hInt : IntegrableOn (fun w : ℂ => C * ‖w‖ ^ (α - 1)) (Metric.ball 0 ρ) volume := by
    refine integrableOn_ball_of_norm_le_rpow (E := ℂ) (F := ℝ) (C := C) (α := 1 - α) (r := ρ)
      (by rw [Complex.finrank_real_complex]; norm_num)
      (by rw [Complex.finrank_real_complex]; push_cast; linarith) ?_ hmeas
    filter_upwards with x
    rw [Real.norm_of_nonneg (by positivity), neg_sub]
  have hbound : ‖∫ w in Metric.ball 0 ρ, (f (z + w) - f z) / w‖
      ≤ ∫ w : ℂ in Metric.ball 0 ρ, C * ‖w‖ ^ (α - 1) :=
    norm_integral_le_of_norm_le hInt (Filter.Eventually.of_forall hpt)
  have hval : (∫ w : ℂ in Metric.ball 0 ρ, C * ‖w‖ ^ (α - 1))
      = 2 * Real.pi * C * ρ ^ (α + 1) / (α + 1) := by
    rw [integral_const_mul, norm_cauchyTransform_le_aux_disc hρ (by linarith : -2 < α - 1)]
    rw [show (α - 1) + 2 = α + 1 from by ring]
    ring
  have hpi2 : Real.pi⁻¹ * (2 * Real.pi) = 2 := by
    rw [mul_comm (2:ℝ) Real.pi, ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]
  calc ‖cauchyTransform ρ f z‖
      = ‖((Real.pi : ℂ))⁻¹‖ * ‖∫ w in Metric.ball 0 ρ, (f (z + w) - f z) / w‖ := by
        simp only [cauchyTransform, norm_mul, norm_neg]
    _ ≤ Real.pi⁻¹ * (∫ w : ℂ in Metric.ball 0 ρ, C * ‖w‖ ^ (α - 1)) := by
        rw [show ‖((Real.pi : ℂ))⁻¹‖ = Real.pi⁻¹ by
          rw [norm_inv]; simp [Real.norm_of_nonneg Real.pi_pos.le]]
        exact mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 2 * C * ρ ^ (α + 1) / (α + 1) := by
        rw [hval]
        rw [show Real.pi⁻¹ * (2 * Real.pi * C * ρ ^ (α + 1) / (α + 1))
            = (Real.pi⁻¹ * (2 * Real.pi)) * (C * ρ ^ (α + 1) / (α + 1)) by ring]
        rw [hpi2]
        ring

end Work.CR.Flat.Cauchy
