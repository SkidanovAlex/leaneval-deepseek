import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Normed.Module.HahnBanach
import Submission.Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_deriv_integral_vector
import Submission.Commons.MeasureTheory.Integral.intervalIntegrable_deriv_of_absolutelyContinuousOnInterval

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option linter.style.haveILetI false

namespace Commons.MeasureTheory.Integral

/-- If `f : ℝ → E` is absolutely continuous on `uIcc a b` with `a ≤ b` and `E` a finite-dimensional
real normed space, then the length of the chord `f b - f a` is bounded by the integral of the norm
of the derivative. This is the fundamental theorem of calculus for absolutely continuous functions
combined with the triangle inequality for the Bochner integral. -/
theorem norm_sub_le_integral_norm_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ‖f b - f a‖ ≤ ∫ t in a..b, ‖deriv f t‖ := by
  obtain ⟨g, _hg1, hg2⟩ := exists_dual_vector'' ℝ (f b - f a)
  have hgac : AbsolutelyContinuousOnInterval (g ∘ f) a b :=
    absolutelyContinuousOnInterval_comp_of_dist_le (norm_nonneg g)
      (fun x y => g.dist_le_opNorm x y) hf
  have hFTC : ∫ t in a..b, deriv (g ∘ f) t = g (f b) - g (f a) := by
    rw [AbsolutelyContinuousOnInterval.integral_deriv_eq_sub hgac]
    rfl
  have hderiv_ae : ∀ᵐ t ∂volume, t ∈ uIoc a b → deriv (g ∘ f) t = g (deriv f t) := by
    filter_upwards [hf.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht htm
    have hdiff : DifferentiableAt ℝ f t := ht (uIoc_subset_uIcc htm)
    have hcd : HasDerivAt (g ∘ f) (g (deriv f t)) t :=
      (ContinuousLinearMap.hasFDerivAt g).comp_hasDerivAt t hdiff.hasDerivAt
    exact hcd.deriv
  have hcongr : ∫ t in a..b, g (deriv f t) = ∫ t in a..b, deriv (g ∘ f) t :=
    (intervalIntegral.integral_congr_ae hderiv_ae).symm
  have hval : ∫ t in a..b, g (deriv f t) = ‖f b - f a‖ := by
    rw [hcongr, hFTC, ← map_sub]
    simpa using hg2
  have hg_int : IntervalIntegrable (fun t => g (deriv f t)) volume a b := by
    have hub : IntervalIntegrable (fun t => deriv (g ∘ f) t) volume a b :=
      AbsolutelyContinuousOnInterval.intervalIntegrable_deriv hgac
    refine hub.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [hderiv_ae] with t ht htm
    exact ht htm
  have hInt1 : IntervalIntegrable (fun t => ‖g (deriv f t)‖) volume a b := hg_int.norm
  have hInt2 : IntervalIntegrable (fun t => ‖deriv f t‖) volume a b :=
    (BoundedVariationOn.intervalIntegrable_deriv_of_finiteDimensional hf.boundedVariationOn).norm
  have hle : ∀ t, ‖g (deriv f t)‖ ≤ ‖deriv f t‖ := by
    intro t
    calc ‖g (deriv f t)‖ ≤ ‖g‖ * ‖deriv f t‖ := g.le_opNorm _
      _ ≤ 1 * ‖deriv f t‖ := by gcongr
      _ = ‖deriv f t‖ := one_mul _
  rw [← hval]
  calc ∫ t in a..b, g (deriv f t)
      ≤ |∫ t in a..b, g (deriv f t)| := le_abs_self _
    _ = ‖∫ t in a..b, g (deriv f t)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t in a..b, ‖g (deriv f t)‖ := intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..b, ‖deriv f t‖ := intervalIntegral.integral_mono hab hInt1 hInt2 hle

/-- Cauchy–Schwarz type bound: for `f` absolutely continuous on `uIcc a b` with `a ≤ b`, the square
of the length of the chord is bounded by the product of the `L²` integral of `‖deriv f‖` over
`(a, b]` and the length `b - a`. -/
theorem ofReal_sq_norm_sub_le_lintegral_sq_deriv_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ENNReal.ofReal (‖f b - f a‖ ^ 2)
      ≤ (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv f t‖ ^ 2)) * ENNReal.ofReal (b - a) := by
  have hA : ‖f b - f a‖ ≤ ∫ t in a..b, ‖deriv f t‖ := norm_sub_le_integral_norm_deriv hab hf
  have haesm : AEStronglyMeasurable (fun t : ℝ => ‖deriv f t‖)
      (volume.restrict (Set.Ioc a b)) := by
    letI : MeasurableSpace E := borel E
    haveI : BorelSpace E := ⟨rfl⟩
    exact ((measurable_deriv f).norm).aestronglyMeasurable
  have hint_eq : ∫ t in a..b, ‖deriv f t‖
      = (∫⁻ t in Set.Ioc a b, ENNReal.ofReal ‖deriv f t‖).toReal := by
    rw [intervalIntegral.integral_of_le hab]
    exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun t => norm_nonneg _)) haesm
  have hW : ENNReal.ofReal ‖f b - f a‖
      ≤ ∫⁻ t in Set.Ioc a b, ENNReal.ofReal ‖deriv f t‖ := by
    calc ENNReal.ofReal ‖f b - f a‖
        ≤ ENNReal.ofReal (∫ t in a..b, ‖deriv f t‖) := ENNReal.ofReal_le_ofReal hA
      _ = ENNReal.ofReal ((∫⁻ t in Set.Ioc a b, ENNReal.ofReal ‖deriv f t‖).toReal) := by
            rw [hint_eq]
      _ ≤ ∫⁻ t in Set.Ioc a b, ENNReal.ofReal ‖deriv f t‖ := ENNReal.ofReal_toReal_le
  have hsq : ENNReal.ofReal (‖f b - f a‖ ^ 2)
      ≤ (∫⁻ t in Set.Ioc a b, ENNReal.ofReal ‖deriv f t‖)
        * (∫⁻ t in Set.Ioc a b, ENNReal.ofReal ‖deriv f t‖) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), pow_two]
    exact mul_le_mul' hW hW
  have hmeas_f : AEMeasurable (fun t : ℝ => ENNReal.ofReal ‖deriv f t‖)
      (volume.restrict (Set.Ioc a b)) := by
    letI : MeasurableSpace E := borel E
    haveI : BorelSpace E := ⟨rfl⟩
    exact (ENNReal.measurable_ofReal.comp (measurable_deriv f).norm).aemeasurable
  have hpq2 : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hHold := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Ioc a b))
    (p := 2) (q := 2) hpq2 hmeas_f (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have hcongr2 : ∫⁻ t in Set.Ioc a b, (ENNReal.ofReal ‖deriv f t‖) ^ (2 : ℝ)
      = ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv f t‖ ^ 2) := by
    refine lintegral_congr fun t => ?_
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have hone : ∫⁻ t in Set.Ioc a b, (1 : ℝ≥0∞) ^ (2 : ℝ) = ENNReal.ofReal (b - a) := by
    simp_rw [ENNReal.one_rpow]
    rw [setLIntegral_one, Real.volume_Ioc]
  have hhalf (x : ℝ≥0∞) : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
    rw [← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num)]
    norm_num
  have hW2 : ∫⁻ t in Set.Ioc a b, ENNReal.ofReal ‖deriv f t‖
      ≤ (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv f t‖ ^ 2)) ^ ((1:ℝ)/2)
        * (ENNReal.ofReal (b - a)) ^ ((1:ℝ)/2) := by
    have h' := hHold
    simp only [Pi.mul_apply, mul_one] at h'
    rw [hcongr2, hone] at h'
    exact h'
  calc ENNReal.ofReal (‖f b - f a‖ ^ 2)
      ≤ (∫⁻ t in Set.Ioc a b, ENNReal.ofReal ‖deriv f t‖)
        * (∫⁻ t in Set.Ioc a b, ENNReal.ofReal ‖deriv f t‖) := hsq
    _ ≤ ((∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv f t‖ ^ 2)) ^ ((1:ℝ)/2)
          * (ENNReal.ofReal (b - a)) ^ ((1:ℝ)/2))
        * ((∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv f t‖ ^ 2)) ^ ((1:ℝ)/2)
          * (ENNReal.ofReal (b - a)) ^ ((1:ℝ)/2)) := mul_le_mul' hW2 hW2
    _ = (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv f t‖ ^ 2)) * ENNReal.ofReal (b - a) := by
        rw [mul_mul_mul_comm, hhalf, hhalf]

theorem ofReal_chord_sq_div_add_le_lintegral_deriv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : ℝ → E} {τ c h : ℝ}
    (hτ : 0 < τ) (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hf : AbsolutelyContinuousOnInterval f 0 τ) :
    ENNReal.ofReal ((1 / 2) * c * ‖f τ - f 0‖ ^ 2 / τ + h * τ)
      ≤ ∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal ((1 / 2) * c * ‖deriv f t‖ ^ 2 + h) := by
  have hab : (0 : ℝ) ≤ τ := hτ.le
  have hc2 : (0 : ℝ) ≤ (1 / 2) * c := by positivity
  have hsq := ofReal_sq_norm_sub_le_lintegral_sq_deriv_mul (a := 0) (b := τ) hab hf
  rw [sub_zero] at hsq
  have hτ0 : ENNReal.ofReal τ ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hτ
  have hτtop : ENNReal.ofReal τ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hY : ENNReal.ofReal (‖f τ - f 0‖ ^ 2 / τ)
      ≤ ∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv f t‖ ^ 2) := by
    rw [ENNReal.ofReal_div_of_pos hτ, div_eq_mul_inv]
    calc ENNReal.ofReal (‖f τ - f 0‖ ^ 2) * (ENNReal.ofReal τ)⁻¹
        ≤ ((∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv f t‖ ^ 2)) * ENNReal.ofReal τ)
            * (ENNReal.ofReal τ)⁻¹ := mul_le_mul' hsq le_rfl
      _ = ∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv f t‖ ^ 2) :=
            ENNReal.mul_inv_cancel_right hτ0 hτtop
  have hA2 : (0 : ℝ) ≤ ‖f τ - f 0‖ ^ 2 / τ := div_nonneg (sq_nonneg _) hab
  have hYeq : ∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal ((1 / 2) * c * ‖deriv f t‖ ^ 2)
      = ENNReal.ofReal ((1 / 2) * c)
        * ∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv f t‖ ^ 2) := by
    simp_rw [ENNReal.ofReal_mul hc2]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hheq : ∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal h = ENNReal.ofReal (h * τ) := by
    rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul hh]
  have hadd : ∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal ((1 / 2) * c * ‖deriv f t‖ ^ 2 + h)
      = ENNReal.ofReal ((1 / 2) * c)
          * (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv f t‖ ^ 2))
        + ENNReal.ofReal (h * τ) := by
    rw [show (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal ((1 / 2) * c * ‖deriv f t‖ ^ 2 + h))
        = ∫⁻ t in Set.Ioc 0 τ,
            (ENNReal.ofReal ((1 / 2) * c * ‖deriv f t‖ ^ 2) + ENNReal.ofReal h) from
          lintegral_congr fun t => ENNReal.ofReal_add (mul_nonneg hc2 (sq_nonneg _)) hh]
    rw [lintegral_add_right' _ aemeasurable_const, hYeq, hheq]
  have harg : (1 / 2) * c * ‖f τ - f 0‖ ^ 2 / τ + h * τ
      = (1 / 2) * c * (‖f τ - f 0‖ ^ 2 / τ) + h * τ := by ring
  rw [harg]
  calc ENNReal.ofReal ((1 / 2) * c * (‖f τ - f 0‖ ^ 2 / τ) + h * τ)
      = ENNReal.ofReal ((1 / 2) * c * (‖f τ - f 0‖ ^ 2 / τ)) + ENNReal.ofReal (h * τ) :=
          ENNReal.ofReal_add (mul_nonneg hc2 hA2) (mul_nonneg hh hab)
    _ = ENNReal.ofReal ((1 / 2) * c) * ENNReal.ofReal (‖f τ - f 0‖ ^ 2 / τ)
          + ENNReal.ofReal (h * τ) := by rw [ENNReal.ofReal_mul hc2]
    _ ≤ ENNReal.ofReal ((1 / 2) * c)
          * (∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal (‖deriv f t‖ ^ 2))
          + ENNReal.ofReal (h * τ) := by gcongr
    _ = ∫⁻ t in Set.Ioc 0 τ, ENNReal.ofReal ((1 / 2) * c * ‖deriv f t‖ ^ 2 + h) := hadd.symm

end Commons.MeasureTheory.Integral