import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.cs_integral
import Submission.Work.Elliptic.hardy_op_L2_tonelli

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- For a nonnegative real function, the Bochner integral is bounded by the `toReal` of the
`lintegral` of `ofReal` (which is `0` for a non-measurable function; the inequality then
holds trivially). -/
theorem integral_le_toReal_lintegral_ofReal {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) (hf : 0 ≤ᵐ[μ] f) :
    ∫ x, f x ∂μ ≤ (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal := by
  by_cases h : AEStronglyMeasurable f μ
  · rw [integral_eq_lintegral_of_nonneg_ae hf h]
  · have hni : ¬ Integrable f μ := fun hi => h hi.aestronglyMeasurable
    rw [integral_undef hni]
    exact ENNReal.toReal_nonneg

/-- **Pointwise (weighted Cauchy–Schwarz) step of the Hardy inequality.**

For `β > 1`, `z > 0` and `f` with `f²` integrable on `(0,∞)`,
`(∫_0^z s^{β-1} f(s) ds)² ≤ (2 z^{β/2}/β) · ∫_0^z s^{(3β-2)/2} f(s)² ds`. -/
theorem hardy_op_L2_pointwise (β : ℝ) (hβ : 1 < β) (f : ℝ → ℝ)
    (hf : IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) {z : ℝ} (hz : 0 < z) :
    (∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2
      ≤ 2 * z ^ (β / 2) / β *
        (∫⁻ s in Set.Ioc 0 z,
          ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal := by
  have hz0 : (0 : ℝ) ≤ z := hz.le
  have hb1 : -1 < (β - 2) / 2 := by linarith
  have hb2 : (0 : ℝ) ≤ (3 * β - 2) / 2 := by linarith
  have hb3 : (0 : ℝ) ≤ (3 * β - 2) / 4 := by linarith
  have hfz : IntegrableOn (fun s : ℝ => f s ^ 2) (Set.Ioc 0 z) :=
    hf.mono_set (fun s hs => hs.1)
  -- Step 1: the interval integral of the norm.
  have h1 : ‖∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s‖
      ≤ ∫ s in (0 : ℝ)..z, ‖s ^ (β - 1) * f s‖ :=
    intervalIntegral.norm_integral_le_integral_norm hz0
  -- Step 2: rewrite the norm integrand as a product.
  have h2 : ∫ s in (0 : ℝ)..z, ‖s ^ (β - 1) * f s‖
      = ∫ s in Set.Ioc 0 z,
          s ^ ((β - 2) / 4) * (s ^ ((3 * β - 2) / 4) * |f s|) := by
    rw [intervalIntegral.integral_of_le hz0]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hs0 : 0 < s := hs.1
    have hsum : (β - 2) / 4 + (3 * β - 2) / 4 = β - 1 := by ring
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hs0 _)]
    rw [← mul_assoc, ← Real.rpow_add hs0, hsum]
  -- Step 3: `L²` Cauchy–Schwarz on `(0,z]`.
  have hAESu : AEStronglyMeasurable (fun s : ℝ => s ^ ((β - 2) / 4))
      (volume.restrict (Set.Ioc 0 z)) := by
    refine ContinuousOn.aestronglyMeasurable (fun s hs => ?_) measurableSet_Ioc
    exact (Real.continuousAt_rpow_const s _ (Or.inl (ne_of_gt hs.1))).continuousWithinAt
  have hu_mem : MemLp (fun s : ℝ => s ^ ((β - 2) / 4)) 2 (volume.restrict (Set.Ioc 0 z)) := by
    rw [memLp_two_iff_integrable_sq hAESu]
    refine IntegrableOn.congr_fun (f := fun s : ℝ => s ^ ((β - 2) / 2)) ?_ ?_ measurableSet_Ioc
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hz0).mp
        (intervalIntegral.intervalIntegrable_rpow' hb1)
    · intro s hs
      change s ^ ((β - 2) / 2) = (s ^ ((β - 2) / 4)) ^ 2
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.1.le]
      congr 1
      ring
  have hAESv : AEStronglyMeasurable (fun s : ℝ => s ^ ((3 * β - 2) / 4) * |f s|)
      (volume.restrict (Set.Ioc 0 z)) := by
    have hs1 : AEStronglyMeasurable (fun s : ℝ => s ^ ((3 * β - 2) / 4))
        (volume.restrict (Set.Ioc 0 z)) :=
      (Real.continuous_rpow_const hb3).aestronglyMeasurable
    have hs2 : AEStronglyMeasurable (fun s : ℝ => |f s|) (volume.restrict (Set.Ioc 0 z)) := by
      have h0 : AEMeasurable (fun s : ℝ => Real.sqrt (f s ^ 2))
          (volume.restrict (Set.Ioc 0 z)) := hfz.aestronglyMeasurable.aemeasurable.sqrt
      refine h0.aestronglyMeasurable.congr ?_
      exact Filter.Eventually.of_forall (fun s => Real.sqrt_sq_eq_abs (f s))
    exact hs1.mul hs2
  have hv_mem : MemLp (fun s : ℝ => s ^ ((3 * β - 2) / 4) * |f s|) 2
      (volume.restrict (Set.Ioc 0 z)) := by
    rw [memLp_two_iff_integrable_sq hAESv]
    refine IntegrableOn.congr_fun
      (f := fun s : ℝ => s ^ ((3 * β - 2) / 2) * f s ^ 2) ?_ ?_ measurableSet_Ioc
    · refine Integrable.mono' (hfz.const_mul (z ^ ((3 * β - 2) / 2))) ?_ ?_
      · have hs1 : AEStronglyMeasurable (fun s : ℝ => s ^ ((3 * β - 2) / 2))
            (volume.restrict (Set.Ioc 0 z)) :=
          (Real.continuous_rpow_const hb2).aestronglyMeasurable
        exact hs1.mul hfz.aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        have hs0 : 0 < s := hs.1
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hs0.le _) (sq_nonneg _))]
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact Real.rpow_le_rpow hs0.le hs.2 hb2
    · intro s hs
      change s ^ ((3 * β - 2) / 2) * f s ^ 2 = (s ^ ((3 * β - 2) / 4) * |f s|) ^ 2
      have hB : (s ^ ((3 * β - 2) / 4)) ^ 2 = s ^ ((3 * β - 2) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs.1.le]
        congr 1
        ring
      rw [mul_pow, sq_abs, hB]
  have hcs := Work.Spaces.cs_integral hu_mem hv_mem
  -- Step 4: the two integrals.
  have hu2 : ∫ s in Set.Ioc 0 z, (s ^ ((β - 2) / 4)) ^ 2 = 2 * z ^ (β / 2) / β := by
    have hB : ∀ s : ℝ, 0 < s → (s ^ ((β - 2) / 4)) ^ 2 = s ^ ((β - 2) / 2) := by
      intro s hs
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
      congr 1
      ring
    have hcongr : ∫ s in Set.Ioc 0 z, (s ^ ((β - 2) / 4)) ^ 2
        = ∫ s in (0 : ℝ)..z, s ^ ((β - 2) / 2) := by
      rw [intervalIntegral.integral_of_le hz0]
      exact setIntegral_congr_fun measurableSet_Ioc (fun s hs => hB s hs.1)
    rw [hcongr, integral_rpow (Or.inl hb1)]
    rw [show (β - 2) / 2 + 1 = β / 2 by ring]
    rw [Real.zero_rpow (by positivity : (β / 2) ≠ 0)]
    have hb0 : β ≠ 0 := by linarith
    field_simp
    ring_nf
  have hv2 : ∫ s in Set.Ioc 0 z, (s ^ ((3 * β - 2) / 4) * |f s|) ^ 2
      = (∫⁻ s in Set.Ioc 0 z,
          ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal := by
    have hB : ∀ s : ℝ, 0 < s → (s ^ ((3 * β - 2) / 4) * |f s|) ^ 2
        = s ^ ((3 * β - 2) / 2) * f s ^ 2 := by
      intro s hs
      have hB' : (s ^ ((3 * β - 2) / 4)) ^ 2 = s ^ ((3 * β - 2) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
        congr 1
        ring
      rw [mul_pow, sq_abs, hB']
    have hcongr : ∫ s in Set.Ioc 0 z, (s ^ ((3 * β - 2) / 4) * |f s|) ^ 2
        = ∫ s in Set.Ioc 0 z, s ^ ((3 * β - 2) / 2) * f s ^ 2 :=
      setIntegral_congr_fun measurableSet_Ioc (fun s hs => hB s hs.1)
    rw [hcongr]
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 z)]
        (fun s : ℝ => s ^ ((3 * β - 2) / 2) * f s ^ 2) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact mul_nonneg (Real.rpow_nonneg hs.1.le _) (sq_nonneg _)
    have hAES : AEStronglyMeasurable (fun s : ℝ => s ^ ((3 * β - 2) / 2) * f s ^ 2)
        (volume.restrict (Set.Ioc 0 z)) := by
      have hs1 : AEStronglyMeasurable (fun s : ℝ => s ^ ((3 * β - 2) / 2))
          (volume.restrict (Set.Ioc 0 z)) :=
        (Real.continuous_rpow_const hb2).aestronglyMeasurable
      exact hs1.mul hfz.aestronglyMeasurable
    exact integral_eq_lintegral_of_nonneg_ae hnn hAES
  -- Assemble.
  have hI0 : (0 : ℝ) ≤ ∫ s in (0 : ℝ)..z, ‖s ^ (β - 1) * f s‖ :=
    intervalIntegral.integral_nonneg hz0 (fun s _ => norm_nonneg _)
  have hsq : (‖∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s‖) ^ 2
      ≤ (∫ s in (0 : ℝ)..z, ‖s ^ (β - 1) * f s‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc (∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2
      = ‖∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s‖ ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
    _ ≤ (∫ s in (0 : ℝ)..z, ‖s ^ (β - 1) * f s‖) ^ 2 := hsq
    _ = (∫ s in Set.Ioc 0 z,
          s ^ ((β - 2) / 4) * (s ^ ((3 * β - 2) / 4) * |f s|)) ^ 2 := by rw [h2]
    _ ≤ (∫ s in Set.Ioc 0 z, (s ^ ((β - 2) / 4)) ^ 2)
          * (∫ s in Set.Ioc 0 z, (s ^ ((3 * β - 2) / 4) * |f s|) ^ 2) := hcs
    _ = 2 * z ^ (β / 2) / β *
          (∫⁻ s in Set.Ioc 0 z,
            ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal := by rw [hu2, hv2]



theorem hardy_operator_L2 (β : ℝ) (hβ : 1 < β) (f : ℝ → ℝ)
    (hf : IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) :
    ∫ z in Set.Ioi (0 : ℝ), (z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2
      ≤ 4 / (β * (3 * β - 2)) * ∫ z in Set.Ioi (0 : ℝ), f z ^ 2 := by
  have hb0 : (0 : ℝ) < β := by linarith
  have hb2 : (0 : ℝ) < 3 * β - 2 := by linarith
  have hJ : 0 ≤ ∫ z in Set.Ioi 0, f z ^ 2 :=
    integral_nonneg (fun z => sq_nonneg (f z))
  have hcomp := integral_le_toReal_lintegral_ofReal (volume.restrict (Set.Ioi 0))
      (fun z => (z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2)
      (Filter.Eventually.of_forall (fun z => sq_nonneg _))
  have hpoint : ∀ z, (Set.Ioi (0 : ℝ)).indicator
        (fun z => ENNReal.ofReal ((z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2)) z
      ≤ ENNReal.ofReal (2 / β) * (Set.Ioi (0 : ℝ)).indicator
        (fun z => ENNReal.ofReal (z ^ (-(3 * β / 2))) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2))) z := by
    intro z
    by_cases hz : z ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
      have hzpos : 0 < z := hz
      have hrz : (z ^ (-β)) ^ 2 = z ^ (-(2 * β)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]
        congr 1
        ring
      have hc3 : z ^ (-(2 * β)) * z ^ (β / 2) = z ^ (-(3 * β / 2)) := by
        rw [← Real.rpow_add hzpos]
        congr 1
        ring
      have hp := hardy_op_L2_pointwise β hβ f hf hzpos
      have hle : (z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2
          ≤ (2 / β) * z ^ (-(3 * β / 2)) *
            (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal := by
        rw [mul_pow, hrz]
        calc z ^ (-(2 * β)) * (∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2
            ≤ z ^ (-(2 * β)) * ((2 * z ^ (β / 2) / β) *
                (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal) :=
              mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hzpos.le _)
          _ = (2 / β) * z ^ (-(3 * β / 2)) *
                (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal := by
              rw [← hc3]
              ring
      refine (ENNReal.ofReal_le_ofReal hle).trans ?_
      rw [show (2 / β) * z ^ (-(3 * β / 2)) *
            (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal
          = (2 / β) * (z ^ (-(3 * β / 2)) *
              (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)).toReal) by ring]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Real.rpow_nonneg hzpos.le _)]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ENNReal.ofReal_toReal_le (bot_le)) (bot_le)
    · rw [Set.indicator_of_notMem hz]
      exact bot_le
  have hstep : (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2))
      ≤ ENNReal.ofReal (2 / β) *
        (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (z ^ (-(3 * β / 2))) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2))) := by
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi,
        ← lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)]
    exact lintegral_mono hpoint
  have hT := hardy_op_L2_tonelli β hβ f hf
  have hfin : ENNReal.ofReal (2 / β) *
        (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (z ^ (-(3 * β / 2))) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2))) ≠ ⊤ := by
    rw [hT]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  calc ∫ z in Set.Ioi (0 : ℝ), (z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2
      ≤ (∫⁻ z in Set.Ioi (0 : ℝ),
          ENNReal.ofReal ((z ^ (-β) * ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s) ^ 2)).toReal := hcomp
    _ ≤ (ENNReal.ofReal (2 / β) *
          (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal (z ^ (-(3 * β / 2))) *
            (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)))).toReal :=
        ENNReal.toReal_mono hfin hstep
    _ = (ENNReal.ofReal (2 / β) *
          ENNReal.ofReal (2 / (3 * β - 2) * ∫ z in Set.Ioi 0, f z ^ 2)).toReal := by rw [hT]
    _ = 4 / (β * (3 * β - 2)) * ∫ z in Set.Ioi (0 : ℝ), f z ^ 2 := by
        have h1 : β ≠ 0 := ne_of_gt hb0
        have h2 : (3 * β - 2) ≠ 0 := ne_of_gt hb2
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
            ENNReal.toReal_ofReal (mul_nonneg (by positivity) hJ)]
        field_simp
        ring

end Work.Elliptic
