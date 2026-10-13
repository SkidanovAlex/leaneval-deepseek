import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The weighted Cauchy–Schwarz bound `(∫_a^b (b - t) f t)² ≤ ((b-a)³/3) ∫ f²`

`Work.FTS.EllipticEst.DzAmgm.OfRealIntervalIntegralSqLe`, in the `lintegral` (i.e.
unconditional, `ℝ≥0∞`-valued) form used by the sliced Agmon–Nirenberg assembly.

The proof is the sharp `L²` Cauchy–Schwarz inequality applied to the pair
`(g, f)`, `g t = b - t`, together with `∫_a^b (b - t)² dt = (b - a)³ / 3`:

`(∫_a^b g f)² ≤ (∫_a^b g²)(∫_a^b f²) = ((b-a)³/3) · ∫_a^b f²`.

No integrability of `f` is assumed: everything is phrased with `lintegral`, using
Hölder's inequality for `ℝ≥0∞`-valued functions in the `p = q = 2` case, which is
unconditional.  Bounding `|∫ (b-t) f t| ≤ ∫⁻ |(b-t) f t|` uses
`MeasureTheory.enorm_integral_le_lintegral_enorm`.
-/

noncomputable section

open scoped ENNReal
open MeasureTheory Set

namespace Work.FTS.EllipticEst.DzAmgm

/-- The plain interval integral of `t ↦ (b - t)²` over `[a, b]` equals `(b - a)³ / 3`. -/
theorem integral_sq_sub_eq (a b : ℝ) : ∫ t in a..b, (b - t) ^ 2 = (b - a) ^ 3 / 3 := by
  have h1 := intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ 2) b (a := a) (b := b)
  -- `h1 : ∫ x in a..b, (b - x)^2 = ∫ x in b - b..b - a, x^2`
  rw [h1, sub_self, integral_pow]
  norm_num

theorem OfRealIntervalIntegralSqLe {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioc a b))) :
    ENNReal.ofReal ((∫ t in a..b, (b - t) * f t) ^ 2)
      ≤ ENNReal.ofReal ((b - a) ^ 3 / 3)
        * ∫⁻ t in Set.Ioc a b, ENNReal.ofReal ((f t) ^ 2) := by
  rw [intervalIntegral.integral_of_le hab]
  -- The two `L²` factors of Cauchy–Schwarz.
  set F : ℝ → ℝ≥0∞ := fun t => ‖b - t‖ₑ with hF
  set H : ℝ → ℝ≥0∞ := fun t => ‖f t‖ₑ with hH
  have hFmeas : AEMeasurable F (volume.restrict (Set.Ioc a b)) := by
    rw [hF]
    exact ((continuous_const.sub continuous_id).aemeasurable).enorm
  have hHmeas : AEMeasurable H (volume.restrict (Set.Ioc a b)) := by
    rw [hH]
    exact hf.enorm
  -- The `L²` norm of the bounded function `t ↦ b - t` is the sharp constant.
  have hF2 : ∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ) = ENNReal.ofReal ((b - a) ^ 3 / 3) := by
    have hpt : ∀ t : ℝ, (F t) ^ (2 : ℝ) = ENNReal.ofReal ((b - t) ^ 2) := by
      intro t
      simp only [hF]
      rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two,
        ← ENNReal.ofReal_pow (abs_nonneg (b - t)) 2, sq_abs]
    simp_rw [hpt]
    have hI : IntegrableOn (fun t : ℝ => (b - t) ^ 2) (Set.Ioc a b) volume :=
      (ContinuousOn.integrableOn_compact isCompact_Icc
        ((continuous_const.sub continuous_id).pow 2).continuousOn).mono_set
        Ioc_subset_Icc_self
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hI
      (Filter.Eventually.of_forall fun t => sq_nonneg (b - t))]
    rw [← intervalIntegral.integral_of_le hab, integral_sq_sub_eq]
  have hH2 : ∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)
      = ∫⁻ t in Set.Ioc a b, ENNReal.ofReal ((f t) ^ 2) := by
    refine lintegral_congr fun t => ?_
    simp only [hH]
    rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (abs_nonneg (f t)) 2, sq_abs]
  -- Cauchy–Schwarz for `ℝ≥0∞`-valued functions, `p = q = 2`.
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hCS : ∫⁻ t in Set.Ioc a b, F t * H t
      ≤ (∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Ioc a b)) hpq hFmeas hHmeas
  -- Squaring Cauchy–Schwarz.
  have hrpow : ((∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ (2 : ℝ)
      = (∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ)) * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 1 / 2 by norm_num),
      ← ENNReal.rpow_mul,
      show (1 : ℝ) / 2 * 2 = 1 by norm_num, ENNReal.rpow_one]
  have hCSsq : (∫⁻ t in Set.Ioc a b, F t * H t) ^ (2 : ℝ)
      ≤ (∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ))
        * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) := by
    have h2 := ENNReal.rpow_le_rpow hCS (show (0 : ℝ) ≤ 2 by norm_num)
    rwa [hrpow] at h2
  -- Bound the absolute value of the integral by the `lintegral` of the product.
  have hInt : ENNReal.ofReal |∫ t in Set.Ioc a b, (b - t) * f t|
      ≤ ∫⁻ t in Set.Ioc a b, F t * H t := by
    have h1 : ‖∫ t in Set.Ioc a b, (b - t) * f t‖ₑ
        ≤ ∫⁻ t in Set.Ioc a b, ‖(b - t) * f t‖ₑ :=
      enorm_integral_le_lintegral_enorm (fun t => (b - t) * f t)
    rw [Real.enorm_eq_ofReal_abs] at h1
    refine h1.trans (le_of_eq ?_)
    refine lintegral_congr fun t => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_mul, ENNReal.ofReal_mul (abs_nonneg (b - t))]
    simp only [hF, hH, Real.enorm_eq_ofReal_abs]
  have hleft : ENNReal.ofReal ((∫ t in Set.Ioc a b, (b - t) * f t) ^ 2)
      ≤ (∫⁻ t in Set.Ioc a b, F t * H t) ^ (2 : ℝ) := by
    have h1 : ENNReal.ofReal ((∫ t in Set.Ioc a b, (b - t) * f t) ^ 2)
        = (ENNReal.ofReal |∫ t in Set.Ioc a b, (b - t) * f t|) ^ 2 := by
      rw [← sq_abs (∫ t in Set.Ioc a b, (b - t) * f t)]
      exact ENNReal.ofReal_pow (abs_nonneg _) 2
    rw [h1, ← ENNReal.rpow_two]
    exact ENNReal.rpow_le_rpow hInt (show (0 : ℝ) ≤ 2 by norm_num)
  calc ENNReal.ofReal ((∫ t in Set.Ioc a b, (b - t) * f t) ^ 2)
      ≤ (∫⁻ t in Set.Ioc a b, F t * H t) ^ (2 : ℝ) := hleft
    _ ≤ (∫⁻ t in Set.Ioc a b, (F t) ^ (2 : ℝ))
        * (∫⁻ t in Set.Ioc a b, (H t) ^ (2 : ℝ)) := hCSsq
    _ = ENNReal.ofReal ((b - a) ^ 3 / 3) * ∫⁻ t in Set.Ioc a b, ENNReal.ofReal ((f t) ^ 2) := by
        rw [hF2, hH2]

end Work.FTS.EllipticEst.DzAmgm
