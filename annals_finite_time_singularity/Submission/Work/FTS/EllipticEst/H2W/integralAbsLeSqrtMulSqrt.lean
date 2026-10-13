import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Hölder (Cauchy–Schwarz) for the interval integral

`∫ t in a..b, |f t| ≤ √(b - a) · √(∫ t in a..b, (f t)²)` for `a < b` and `f` interval
integrable together with its square.

This is Hölder's inequality with conjugate exponents `p = q = 2` applied to the pair
`(|f|, 1)` on the finite measure `volume.restrict (Ioc a b)`, together with
`volume.real (Ioc a b) = b - a` and `|f t|² = (f t)²`.
-/

namespace Work.FTS.EllipticEst.H2W

open MeasureTheory Set Filter

theorem integralAbsLeSqrtMulSqrt {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hf2 : IntervalIntegrable (fun t => (f t) ^ 2) MeasureTheory.volume a b) :
    (∫ t in a..b, |f t|) ≤ Real.sqrt (b - a) * Real.sqrt (∫ t in a..b, (f t) ^ 2) := by
  have hab' : a ≤ b := hab.le
  -- work on the restricted measure `volume.restrict (Ioc a b)`
  have hfI : IntegrableOn f (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab').mp hf
  have hf2I : IntegrableOn (fun t => (f t) ^ 2) (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab').mp hf2
  have hfm : AEStronglyMeasurable (fun t => |f t|) (volume.restrict (Ioc a b)) :=
    continuous_abs.comp_aestronglyMeasurable hfI.aestronglyMeasurable
  have hsq : Integrable (fun t => |f t| ^ 2) (volume.restrict (Ioc a b)) :=
    hf2I.congr (Eventually.of_forall fun t => (sq_abs (f t)).symm)
  have hmem : MemLp (fun t => |f t|) (ENNReal.ofReal 2) (volume.restrict (Ioc a b)) := by
    have h : MemLp (fun t => |f t|) 2 (volume.restrict (Ioc a b)) :=
      (memLp_two_iff_integrable_sq hfm).2 hsq
    simpa using h
  have hone : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2)
      (volume.restrict (Ioc a b)) :=
    memLp_const (1 : ℝ)
  -- Hölder with `p = q = 2` for the pair `(|f|, 1)`
  have hhold := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Ioc a b))
    (p := 2) (q := 2) Real.HolderConjugate.two_two
    (f := fun t => |f t|) (g := fun _ => (1 : ℝ))
    (Eventually.of_forall fun _ => abs_nonneg _)
    (Eventually.of_forall fun _ => zero_le_one) hmem hone
  have h1 : (∫ t in Ioc a b, |f t| * 1) = ∫ t in Ioc a b, |f t| := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp
  have h2 : (∫ t in Ioc a b, |f t| ^ (2 : ℝ)) = ∫ t in Ioc a b, (f t) ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp [sq_abs]
  have h3 : (∫ t in Ioc a b, (1 : ℝ) ^ (2 : ℝ)) = b - a := by
    have hone' : (∫ t in Ioc a b, (1 : ℝ) ^ (2 : ℝ)) = ∫ t in Ioc a b, (1 : ℝ) := by
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp
    rw [hone', setIntegral_const, measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab'), smul_eq_mul, mul_one]
  rw [h2, h3] at hhold
  rw [intervalIntegral.integral_of_le hab', intervalIntegral.integral_of_le hab']
  have hh : (∫ t in Ioc a b, |f t|)
      ≤ (∫ t in Ioc a b, (f t) ^ 2) ^ (1 / 2 : ℝ) * (b - a) ^ (1 / 2 : ℝ) := h1 ▸ hhold
  have hsqrt : (∫ t in Ioc a b, (f t) ^ 2) ^ (1 / 2 : ℝ) * (b - a) ^ (1 / 2 : ℝ)
      = Real.sqrt (b - a) * Real.sqrt (∫ t in Ioc a b, (f t) ^ 2) := by
    rw [Real.sqrt_eq_rpow (b - a), Real.sqrt_eq_rpow (∫ t in Ioc a b, (f t) ^ 2)]
    exact mul_comm _ _
  exact hh.trans_eq hsqrt

end Work.FTS.EllipticEst.H2W
