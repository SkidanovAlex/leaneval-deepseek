import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.GbarSetup
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.FTS.EllipticEst

/-! ## Pointwise `L²` bound for the weighted Hardy operator `HarOp`

This file proves

  `(HarOp β f z) ^ 2 ≤ (1 / β) * z ^ (-β) * ∫⁻ s in (0,z], s ^ (β - 1) * f s ^ 2`

(as an inequality in `ℝ≥0∞`), for `β > 1`, `z > 0` and `f` with `f ^ 2` integrable on `(0,∞)`.

The mathematical content is the weighted Cauchy–Schwarz inequality

  `(∫_0^z s ^ (β - 1) f s) ^ 2 ≤ (∫_0^z s ^ (β - 1)) * (∫_0^z s ^ (β - 1) f s ^ 2)`

together with `∫_0^z s ^ (β - 1) = z ^ β / β`.

Note that `f` is *not* assumed measurable: only `f ^ 2` is.  We therefore never use `f` itself
as a measurable function; the `|f|` that appears in Cauchy–Schwarz is written as `√(f ^ 2)` (the
definition `absF` below), which is a.e. strongly measurable as soon as `f ^ 2` is. -/

/-- `s ↦ √(f s ^ 2)`, i.e. `|f s|` in a form that is a.e. strongly measurable as soon as
`f ^ 2` is. -/
def absF (f : ℝ → ℝ) : ℝ → ℝ := fun s => Real.sqrt (f s ^ 2)

theorem absF_eq_abs (f : ℝ → ℝ) (s : ℝ) : absF f s = |f s| := Real.sqrt_sq_eq_abs (f s)

theorem absF_nonneg (f : ℝ → ℝ) (s : ℝ) : 0 ≤ absF f s := Real.sqrt_nonneg _

theorem absF_sq (f : ℝ → ℝ) (s : ℝ) : absF f s ^ 2 = f s ^ 2 := by
  rw [absF_eq_abs, sq_abs]

/-- `(x ^ y) ^ 2 = x ^ (y + y)` for `x > 0`, for the real power `x ^ y`. -/
theorem sq_rpow {x : ℝ} (hx : 0 < x) (y : ℝ) : (x ^ y) ^ 2 = x ^ (y + y) := by
  rw [pow_two, Real.rpow_add hx]

theorem abs_le_one_add_sq (x : ℝ) : |x| ≤ 1 + x ^ 2 := by
  nlinarith [sq_nonneg (|x| - 1 / 2), sq_abs x]

/-- `∫ s in 0..z, s ^ (β - 1) = z ^ β / β` for `β > 0`. -/
theorem intervalIntegral_rpow_sub_one {β z : ℝ} (hβ : 0 < β) :
    ∫ s in (0 : ℝ)..z, s ^ (β - 1) = z ^ β / β := by
  have h1 : β - 1 + 1 = β := by ring
  rw [integral_rpow (a := 0) (b := z) (r := β - 1) (Or.inl (by linarith)), h1,
    Real.zero_rpow (ne_of_gt hβ)]
  ring

/-- Cauchy–Schwarz in squared form for the Bochner integral of two real functions (no sign
hypothesis is needed: `|∫ a * b| ≤ ∫ |a| * |b| ≤ (∫ a²)^{1/2} (∫ b²)^{1/2}`). -/
theorem sq_integral_mul_le_general {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    {a b : α → ℝ} (ha' : AEStronglyMeasurable a μ) (hb' : AEStronglyMeasurable b μ)
    (ha : MeasureTheory.Integrable (fun s => a s ^ 2) μ)
    (hb : MeasureTheory.Integrable (fun s => b s ^ 2) μ)
    (hab : MeasureTheory.Integrable (fun s => a s * b s) μ) :
    (MeasureTheory.integral μ (fun s => a s * b s)) ^ 2 ≤
      (MeasureTheory.integral μ (fun s => a s ^ 2)) *
        (MeasureTheory.integral μ (fun s => b s ^ 2)) := by
  have hAabs : AEStronglyMeasurable (fun x => |a x|) μ := by
    simpa only [Real.norm_eq_abs] using ha'.norm
  have hBabs : AEStronglyMeasurable (fun x => |b x|) μ := by
    simpa only [Real.norm_eq_abs] using hb'.norm
  have hAi : Integrable (fun x => |a x| ^ 2) μ :=
    ha.congr (Filter.Eventually.of_forall fun x => (sq_abs (a x)).symm)
  have hBi : Integrable (fun x => |b x| ^ 2) μ :=
    hb.congr (Filter.Eventually.of_forall fun x => (sq_abs (b x)).symm)
  have hA' : MemLp (fun x => |a x|) 2 μ := (memLp_two_iff_integrable_sq hAabs).mpr hAi
  have hB' : MemLp (fun x => |b x|) 2 μ := (memLp_two_iff_integrable_sq hBabs).mpr hBi
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) hpq
    (Filter.Eventually.of_forall fun x => abs_nonneg (a x))
    (Filter.Eventually.of_forall fun x => abs_nonneg (b x))
    (by rw [ENNReal.ofReal_ofNat]; exact hA')
    (by rw [ENNReal.ofReal_ofNat]; exact hB')
  have hA2eq : (∫ x, |a x| ^ (2 : ℝ) ∂μ) = ∫ x, a x ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.rpow_ofNat, sq_abs]
  have hB2eq : (∫ x, |b x| ^ (2 : ℝ) ∂μ) = ∫ x, b x ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.rpow_ofNat, sq_abs]
  rw [hA2eq, hB2eq] at hholder
  have hAB : |∫ x, a x * b x ∂μ| ≤
      (∫ x, a x ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ x, b x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
    calc |∫ x, a x * b x ∂μ| ≤ ∫ x, |a x * b x| ∂μ := abs_integral_le_integral_abs
      _ = ∫ x, |a x| * |b x| ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            rw [abs_mul]
      _ ≤ _ := hholder
  have hsq : ((∫ x, a x ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ x, b x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2
      = (∫ x, a x ^ 2 ∂μ) * (∫ x, b x ^ 2 ∂μ) := by
    have hAn : 0 ≤ ∫ x, a x ^ 2 ∂μ :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg (a x))
    have hBn : 0 ≤ ∫ x, b x ^ 2 ∂μ :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall fun x => sq_nonneg (b x))
    rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hAn, Real.sq_sqrt hBn]
  calc (∫ x, a x * b x ∂μ) ^ 2 = |∫ x, a x * b x ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ ((∫ x, a x ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ x, b x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hAB 2
    _ = (∫ x, a x ^ 2 ∂μ) * (∫ x, b x ^ 2 ∂μ) := hsq

theorem HarOp_pointwise_sq (β : ℝ) (hβ : 1 < β) (f : ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) {z : ℝ} (hz : 0 < z) :
    ENNReal.ofReal ((Work.FTS.EllipticEst.HarOp β f z) ^ 2)
      ≤ ENNReal.ofReal (1 / β) * ENNReal.ofReal (z ^ (-β)) *
        ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) := by
  have hβ0 : 0 < β := one_pos.trans hβ
  have hb1 : 0 ≤ β - 1 := by linarith
  have hb1' : 0 < β - 1 := by linarith
  have hb2 : 0 ≤ (β - 1) / 2 := by linarith
  have hb2' : 0 < (β - 1) / 2 := by linarith
  have hz0 : 0 ≤ z := hz.le
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  set I : ℝ := ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s with hI
  set J2 : ℝ := ∫ s in (0 : ℝ)..z, s ^ (β - 1) * f s ^ 2 with hJ2
  -- integrability of `f ^ 2` on `(0, z]`
  have hf2 : Integrable (fun s : ℝ => f s ^ 2) (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    hf.mono_set Set.Ioc_subset_Ioi_self
  -- a dominating integrable function
  have hM : Integrable (fun s : ℝ => z ^ (β - 1) + z ^ (β - 1) * f s ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    (integrable_const _).add (hf2.const_mul _)
  -- `|f|`, as the a.e. strongly measurable function `√(f ^ 2)`
  have hφ : AEStronglyMeasurable (absF f) (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hf2.aestronglyMeasurable
  have hcont : AEStronglyMeasurable (fun s : ℝ => s ^ ((β - 1) / 2))
      (volume.restrict (Set.Ioc (0 : ℝ) z)) :=
    (Real.continuous_rpow_const hb2).aestronglyMeasurable
  -- ## The three integrability assumptions of Cauchy–Schwarz
  have ha : Integrable (fun s : ℝ => (s ^ ((β - 1) / 2)) ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    refine Integrable.mono' hM ((Real.continuous_rpow_const hb2).pow 2).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : 0 < x := hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (x ^ ((β - 1) / 2))), sq_rpow hx0,
      show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]
    calc x ^ (β - 1) ≤ z ^ (β - 1) := Real.rpow_le_rpow hx0.le hx.2 hb1
      _ ≤ z ^ (β - 1) + z ^ (β - 1) * f x ^ 2 :=
          le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hz0 _) (sq_nonneg _))
  have hb : Integrable (fun s : ℝ => (s ^ ((β - 1) / 2) * absF f s) ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    refine Integrable.mono' hM ((hcont.mul hφ).pow 2) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : 0 < x := hx.1
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (x ^ ((β - 1) / 2) * absF f x)),
      mul_pow, sq_rpow hx0, absF_sq,
      show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]
    calc x ^ (β - 1) * f x ^ 2 ≤ z ^ (β - 1) * f x ^ 2 :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx0.le hx.2 hb1) (sq_nonneg _)
      _ ≤ z ^ (β - 1) + z ^ (β - 1) * f x ^ 2 :=
          le_add_of_nonneg_left (Real.rpow_nonneg hz0 _)
  have hab : Integrable (fun s : ℝ => s ^ ((β - 1) / 2) * (s ^ ((β - 1) / 2) * absF f s))
      (volume.restrict (Set.Ioc (0 : ℝ) z)) := by
    refine Integrable.mono' hM (hcont.mul (hcont.mul hφ)) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx0 : 0 < x := hx.1
    have hxp : 0 ≤ x ^ ((β - 1) / 2) := Real.rpow_nonneg hx0.le _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hxp, abs_mul, abs_of_nonneg hxp,
      abs_of_nonneg (absF_nonneg f x), absF_eq_abs,
      show x ^ ((β - 1) / 2) * (x ^ ((β - 1) / 2) * |f x|)
          = (x ^ ((β - 1) / 2) * x ^ ((β - 1) / 2)) * |f x| from by ring,
      show x ^ ((β - 1) / 2) * x ^ ((β - 1) / 2) = x ^ (β - 1) from by
        rw [← Real.rpow_add hx0]; congr 1; ring]
    calc x ^ (β - 1) * |f x| ≤ z ^ (β - 1) * |f x| :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx0.le hx.2 hb1) (abs_nonneg _)
      _ ≤ z ^ (β - 1) * (1 + f x ^ 2) :=
          mul_le_mul_of_nonneg_left (abs_le_one_add_sq (f x)) (Real.rpow_nonneg hz0 _)
      _ = z ^ (β - 1) + z ^ (β - 1) * f x ^ 2 := by ring
  -- ## Cauchy–Schwarz
  have hcs := sq_integral_mul_le_general (volume.restrict (Set.Ioc (0 : ℝ) z))
    (a := fun s : ℝ => s ^ ((β - 1) / 2)) (b := fun s : ℝ => s ^ ((β - 1) / 2) * absF f s)
    hcont (hcont.mul hφ) ha hb hab
  have hA : (∫ s in Set.Ioc (0 : ℝ) z, s ^ ((β - 1) / 2) * (s ^ ((β - 1) / 2) * absF f s))
      = ∫ s in (0 : ℝ)..z, s ^ (β - 1) * absF f s := by
    have h1 : (∫ s in Set.Ioc (0 : ℝ) z,
          s ^ ((β - 1) / 2) * (s ^ ((β - 1) / 2) * absF f s))
        = ∫ s in Set.Ioc (0 : ℝ) z, s ^ (β - 1) * absF f s :=
      setIntegral_congr_fun measurableSet_Ioc (fun x hx => by
        have h2 : x ^ ((β - 1) / 2) * x ^ ((β - 1) / 2) = x ^ (β - 1) := by
          rw [← Real.rpow_add hx.1]; congr 1; ring
        rw [show x ^ ((β - 1) / 2) * (x ^ ((β - 1) / 2) * absF f x)
            = (x ^ ((β - 1) / 2) * x ^ ((β - 1) / 2)) * absF f x from by ring, h2])
    rw [h1, ← intervalIntegral.integral_of_le hz0]
  have hB : (∫ s in Set.Ioc (0 : ℝ) z, (s ^ ((β - 1) / 2)) ^ 2) = z ^ β / β := by
    have h1 : (∫ s in Set.Ioc (0 : ℝ) z, (s ^ ((β - 1) / 2)) ^ 2)
        = ∫ s in Set.Ioc (0 : ℝ) z, s ^ (β - 1) := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
      rcases eq_or_lt_of_le hx.1.le with h | h
      · rw [← h, Real.zero_rpow (ne_of_gt hb2'), Real.zero_rpow (ne_of_gt hb1')]
        norm_num
      · rw [sq_rpow h, show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]
    rw [h1, ← intervalIntegral.integral_of_le hz0]
    exact intervalIntegral_rpow_sub_one hβ0
  have hC : (∫ s in Set.Ioc (0 : ℝ) z, (s ^ ((β - 1) / 2) * absF f s) ^ 2) = J2 := by
    have h1 : (∫ s in Set.Ioc (0 : ℝ) z, (s ^ ((β - 1) / 2) * absF f s) ^ 2)
        = ∫ s in Set.Ioc (0 : ℝ) z, s ^ (β - 1) * f s ^ 2 := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
      rw [mul_pow, sq_rpow hx.1, absF_sq,
        show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]
    rw [h1, hJ2]
    exact (intervalIntegral.integral_of_le hz0).symm
  have hCS : (∫ s in (0 : ℝ)..z, s ^ (β - 1) * absF f s) ^ 2 ≤ (z ^ β / β) * J2 := by
    have h := hcs
    rw [hA, hB, hC] at h
    exact h
  -- ## The integral itself
  have hJle : |I| ≤ ∫ s in (0 : ℝ)..z, s ^ (β - 1) * absF f s := by
    have h1 := intervalIntegral.norm_integral_le_integral_norm
      (μ := volume) (f := fun s : ℝ => s ^ (β - 1) * f s) hz0
    rw [← hI, Real.norm_eq_abs, intervalIntegral.integral_of_le hz0] at h1
    refine h1.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_of_le hz0]
    refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.1.le (β - 1)), absF_eq_abs]
  have hI2 : I ^ 2 ≤ (z ^ β / β) * J2 := by
    have h2 : |I| ^ 2 ≤ (∫ s in (0 : ℝ)..z, s ^ (β - 1) * absF f s) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg I) hJle 2
    rw [sq_abs] at h2
    linarith [hCS, h2]
  -- ## The a.e. bridge to the Lebesgue integral
  have hgI : IntegrableOn (fun s : ℝ => s ^ (β - 1) * f s ^ 2) (Set.Ioc 0 z) :=
    hb.congr ((ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun x hx => by
        show (x ^ ((β - 1) / 2) * absF f x) ^ 2 = x ^ (β - 1) * f x ^ 2
        rw [mul_pow, sq_rpow hx.1, absF_sq,
          show ((β - 1) / 2 + (β - 1) / 2) = β - 1 from by ring]))
  have hbridge : ENNReal.ofReal J2
      = ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) := by
    rw [hJ2, intervalIntegral.integral_of_le hz0]
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgI
      ((ae_restrict_iff' measurableSet_Ioc).mpr
        (Filter.Eventually.of_forall fun x hx =>
          mul_nonneg (Real.rpow_nonneg hx.1.le _) (sq_nonneg (f x))))
  -- ## Final assembly
  have huz : z ^ (-β) * z ^ β = 1 := by
    rw [← Real.rpow_add hz, show -β + β = 0 from by ring, Real.rpow_zero]
  have hmain : (HarOp β f z) ^ 2 = (z ^ (-β)) ^ 2 * I ^ 2 := by
    rw [HarOp, ← hI]
    ring
  have hkey : (z ^ (-β)) ^ 2 * ((z ^ β / β) * J2) = (1 / β) * (z ^ (-β) * J2) := by
    have h1 : (z ^ (-β)) ^ 2 * z ^ β = z ^ (-β) := by
      have h2 : (z ^ (-β)) ^ 2 * z ^ β = z ^ (-β) * (z ^ (-β) * z ^ β) := by ring
      rw [h2, huz, mul_one]
    have h3 : (z ^ (-β)) ^ 2 * ((z ^ β / β) * J2)
        = ((z ^ (-β)) ^ 2 * z ^ β) * (J2 / β) := by ring
    rw [h3, h1]
    ring
  calc ENNReal.ofReal ((HarOp β f z) ^ 2)
      = ENNReal.ofReal ((z ^ (-β)) ^ 2 * I ^ 2) := by rw [hmain]
    _ ≤ ENNReal.ofReal ((z ^ (-β)) ^ 2 * ((z ^ β / β) * J2)) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left hI2 (sq_nonneg _)
    _ = ENNReal.ofReal (1 / β) * ENNReal.ofReal (z ^ (-β)) * ENNReal.ofReal J2 := by
        rw [hkey, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (Real.rpow_nonneg hz0 (-β))]
        ring
    _ = ENNReal.ofReal (1 / β) * ENNReal.ofReal (z ^ (-β)) *
          ∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ (β - 1) * f s ^ 2) := by
        rw [hbridge]

end Work.FTS.EllipticEst
