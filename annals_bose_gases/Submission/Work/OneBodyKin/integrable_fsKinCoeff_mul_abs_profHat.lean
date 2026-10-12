import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.ProfHatDecay
import Submission.Work.OneBodyKin.integrable_chiMul_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.OneBodyKin

open MeasureTheory

/-!
# `Work.OneBodyKin.integrable_fsKinCoeff_mul_abs_profHat`

The `fsKinCoeff`-weighted bump profile `p ↦ [‖p‖ − C]₊² · |profHat p|` is Lebesgue integrable
on `ℝ³`.

Both factors are continuous, so only the behaviour at infinity matters.  There

* `ProfHatDecay` gives `|profHat p| ≤ K (1 + ‖p‖)⁻⁶`;
* `fsKinCoeff C ‖p‖ = max (‖p‖ − C) 0 ^ 2 ≤ (1 + |C|)² (1 + ‖p‖)²`,

so the product is dominated by `(1 + |C|)² K (1 + ‖p‖)⁻⁴`, which is integrable on `ℝ³`
because the exponent `4` exceeds the dimension `3` (`integrable_one_add_norm`).
-/

theorem integrable_fsKinCoeff_mul_abs_profHat (C : ℝ) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff C ‖p‖ * |profHat p|) := by
  obtain ⟨K, hK0, hK⟩ := ProfHatDecay
  -- Integrability of the dominating function `p ↦ (1 + |C|)² K / (1 + ‖p‖)⁴`.
  have hgint : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin 3) => (1 + |C|) ^ 2 * K / (1 + ‖p‖) ^ 4) := by
    have hint : MeasureTheory.Integrable
        (fun p : EuclideanSpace ℝ (Fin 3) => (1 + ‖p‖) ^ (-(4 : ℝ))) := by
      apply integrable_one_add_norm
      norm_num [EuclideanSpace]
    have h2 := hint.const_mul ((1 + |C|) ^ 2 * K)
    refine h2.congr ?_
    filter_upwards with p
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖p‖)]
    rw [show ((1 + ‖p‖ : ℝ) ^ (4 : ℝ)) = (1 + ‖p‖) ^ 4 from Real.rpow_natCast _ 4]
    rw [div_eq_mul_inv]
  refine MeasureTheory.Integrable.mono' hgint ?_ ?_
  · -- continuity of the integrand
    have h1 : Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.fsKinCoeff C ‖p‖) := by
      unfold Submission.BoseGases.fsKinCoeff
      fun_prop
    exact (h1.mul continuous_profHat.abs).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_of_nonneg
      (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg C ‖p‖) (abs_nonneg _))]
    have hx : (0 : ℝ) < 1 + ‖p‖ := by positivity
    -- the `fsKinCoeff` factor is at most `(1 + |C|)² (1 + ‖p‖)²`
    have hfs : Submission.BoseGases.fsKinCoeff C ‖p‖ ≤ (1 + |C|) ^ 2 * (1 + ‖p‖) ^ 2 := by
      unfold Submission.BoseGases.fsKinCoeff
      have h2 : max (‖p‖ - C) 0 ≤ (1 + |C|) * (1 + ‖p‖) := by
        have h1 : ‖p‖ - C ≤ (1 + |C|) * (1 + ‖p‖) := by
          have h3 := neg_le_abs C
          nlinarith [norm_nonneg p, abs_nonneg C,
            mul_nonneg (by positivity : (0 : ℝ) ≤ 1 + |C|) (norm_nonneg p)]
        exact max_le h1 (by positivity)
      have h0 : 0 ≤ max (‖p‖ - C) 0 := le_max_right _ _
      calc max (‖p‖ - C) 0 ^ 2 ≤ ((1 + |C|) * (1 + ‖p‖)) ^ 2 := pow_le_pow_left₀ h0 h2 2
        _ = (1 + |C|) ^ 2 * (1 + ‖p‖) ^ 2 := by rw [mul_pow]
    have h1 : Submission.BoseGases.fsKinCoeff C ‖p‖ * |profHat p|
        ≤ ((1 + |C|) ^ 2 * (1 + ‖p‖) ^ 2) * (K / (1 + ‖p‖) ^ 6) :=
      mul_le_mul hfs (hK p) (abs_nonneg _) (by positivity)
    refine h1.trans (le_of_eq ?_)
    rw [show (1 + ‖p‖) ^ 6 = (1 + ‖p‖) ^ 2 * (1 + ‖p‖) ^ 4 by ring]
    field_simp

end Work.OneBodyKin
