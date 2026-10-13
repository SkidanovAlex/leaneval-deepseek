import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS_RegExport.RXT.SysAux.FK_L12_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXT.SysAux

open MeasureTheory Set

/-!
# Tail bound for the `L12` weight

If `g` is integrable on `(0,∞)`, has *vanishing total integral* `∫_{(0,∞)} g = 0`, and obeys the
pointwise bound `|g r| ≤ B √r / (1+r)²`, then the tail integral over `(z,∞)` satisfies

  `|∫_{(z,∞)} g| ≤ 8 B z^{3/2} / (1+z)²`.

This is the sharp form of the crude bound `|∫_{(z,∞)} g| ≤ B z^{3/2}` (which one gets from
`∫_{(z,∞)} g = -∫_{(0,z]} g` together with the pointwise bound `|g r| ≤ B √z` on `(0,z]`):
the crude bound is useless for large `z`, where the weight `√r/(1+r)² ≍ r^{-3/2}` actually makes
the tail decay like `z^{-1/2}`.

The proof therefore splits into two regimes.

* **`z ≤ 1`**: use the head integral `∫_{(0,z]} g = -∫_{(z,∞)} g` and the crude bound
  `B z^{3/2}` (this is `abs_setIntegral_Ioi_le_of_integral_zero_aux`); since `(1+z)² ≤ 4` here,
  `B z^{3/2} ≤ 8 B z^{3/2}/(1+z)²`.
* **`z ≥ 1`**: bound the tail directly,
  `|∫_{(z,∞)} g| ≤ ∫_{(z,∞)} B√r/(1+r)² ≤ B ∫_{(z,∞)} r^{-3/2} = 2 B z^{-1/2}`,
  and `2 z^{-1/2} ≤ 8 z^{3/2}/(1+z)²` because `(1+z)² ≤ 4 z²` for `z ≥ 1`.
-/

/-- The tail bound, in the regime `z ≤ 1`, obtained from the head integral. -/
private lemma L12_tail_small {g : ℝ → ℝ} {B z : ℝ}
    (hB : 0 ≤ B) (hz : 0 < z) (hz1 : z ≤ 1)
    (hint : MeasureTheory.IntegrableOn g (Set.Ioi 0))
    (hbd : ∀ r : ℝ, 0 < r → |g r| ≤ B * (Real.sqrt r / (1 + r) ^ 2))
    (h0 : ∫ r in Set.Ioi 0, g r = 0) :
    |∫ r in Set.Ioi z, g r| ≤ 8 * B * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
  have hden : (0 : ℝ) < (1 + z) ^ 2 := by positivity
  have hr : (0 : ℝ) < z ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hz _
  -- `(1+z)^2 ≤ 4 ≤ 8`, so `1 ≤ 8/(1+z)^2`
  have hle : (1 : ℝ) ≤ 8 / (1 + z) ^ 2 := by
    rw [le_div_iff₀ hden]
    nlinarith
  calc |∫ r in Set.Ioi z, g r| ≤ B * z ^ ((3 : ℝ) / 2) :=
        abs_setIntegral_Ioi_le_of_integral_zero_aux hB hz hint hbd h0
    _ ≤ B * ((8 / (1 + z) ^ 2) * z ^ ((3 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hr.le hle) hB
    _ = 8 * B * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by ring

/-- The tail bound, in the regime `z ≥ 1`, obtained by bounding the tail integral directly
against `∫_{(z,∞)} r^{-3/2} = 2 z^{-1/2}`. -/
private lemma L12_tail_large {g : ℝ → ℝ} {B z : ℝ}
    (hB : 0 ≤ B) (hz : 0 < z) (hz1 : 1 ≤ z)
    (hint : MeasureTheory.IntegrableOn g (Set.Ioi 0))
    (hbd : ∀ r : ℝ, 0 < r → |g r| ≤ B * (Real.sqrt r / (1 + r) ^ 2)) :
    |∫ r in Set.Ioi z, g r| ≤ 8 * B * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
  have hzle : (0 : ℝ) ≤ z := le_of_lt hz
  have hInt_z : MeasureTheory.IntegrableOn g (Set.Ioi z) :=
    hint.mono_set (Set.Ioi_subset_Ioi hzle)
  have hAbs : MeasureTheory.IntegrableOn (fun r : ℝ => |g r|) (Set.Ioi z) :=
    MeasureTheory.Integrable.abs hInt_z
  -- the comparison function `√r/(1+r)²` is integrable on `(z,∞)`
  have hPhi_int : MeasureTheory.IntegrableOn (fun r : ℝ => Real.sqrt r / (1 + r) ^ 2)
      (Set.Ioi z) := by
    refine MeasureTheory.Integrable.mono'
      (integrableOn_Ioi_rpow_of_lt (a := -(3 : ℝ) / 2) (c := z) (by norm_num) hz) ?_ ?_
    · exact (Real.continuous_sqrt.measurable.div (by fun_prop)).aestronglyMeasurable.restrict
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with r hr
      have hr0 : (0 : ℝ) < r := lt_trans hz hr
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hstep : Real.sqrt r / (1 + r) ^ 2 ≤ Real.sqrt r / r ^ 2 :=
        div_le_div_of_nonneg_left (Real.sqrt_nonneg r) (by positivity) (by nlinarith)
      have heq : Real.sqrt r / r ^ 2 = r ^ (-(3 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast r 2, ← Real.rpow_sub hr0]
        norm_num
      linarith [hstep, heq.le]
  have hIntB : MeasureTheory.IntegrableOn (fun r : ℝ => B * (Real.sqrt r / (1 + r) ^ 2))
      (Set.Ioi z) := MeasureTheory.Integrable.const_mul hPhi_int B
  have hRpow_int : MeasureTheory.IntegrableOn (fun r : ℝ => r ^ (-(3 : ℝ) / 2)) (Set.Ioi z) :=
    integrableOn_Ioi_rpow_of_lt (a := -(3 : ℝ) / 2) (c := z) (by norm_num) hz
  have hstep2 : ∫ r in Set.Ioi z, |g r|
      ≤ ∫ r in Set.Ioi z, B * (Real.sqrt r / (1 + r) ^ 2) :=
    MeasureTheory.setIntegral_mono_on hAbs hIntB measurableSet_Ioi
      (fun r hr => hbd r (lt_trans hz hr))
  have hstep4 : ∫ r in Set.Ioi z, (Real.sqrt r / (1 + r) ^ 2)
      ≤ ∫ r in Set.Ioi z, r ^ (-(3 : ℝ) / 2) := by
    refine MeasureTheory.setIntegral_mono_on hPhi_int hRpow_int measurableSet_Ioi
      (fun r hr => ?_)
    have hr0 : (0 : ℝ) < r := lt_trans hz hr
    have hstep : Real.sqrt r / (1 + r) ^ 2 ≤ Real.sqrt r / r ^ 2 :=
      div_le_div_of_nonneg_left (Real.sqrt_nonneg r) (by positivity) (by nlinarith)
    have heq : Real.sqrt r / r ^ 2 = r ^ (-(3 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast r 2, ← Real.rpow_sub hr0]
      norm_num
    linarith [hstep, heq.le]
  have hstep5 : ∫ r in Set.Ioi z, r ^ (-(3 : ℝ) / 2) = 2 * z ^ (-(1 : ℝ) / 2) := by
    rw [integral_Ioi_rpow_of_lt (a := -(3 : ℝ) / 2) (c := z) (by norm_num) hz]
    have h : (-(3 : ℝ) / 2 + 1) = (-(1 : ℝ) / 2) := by norm_num
    rw [h]
    ring
  have hard : 2 * z ^ (-(1 : ℝ) / 2) ≤ 8 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
    have hs : 0 < Real.sqrt z := Real.sqrt_pos.mpr hz
    have hsq : Real.sqrt z * Real.sqrt z = z := Real.mul_self_sqrt hz.le
    have h32 : z ^ ((3 : ℝ) / 2) = Real.sqrt z * z := by
      rw [Real.sqrt_eq_rpow, show ((3 : ℝ) / 2) = (1 : ℝ) / 2 + 1 by norm_num,
        Real.rpow_add hz, Real.rpow_one]
    have hm : z ^ (-(1 : ℝ) / 2) = (Real.sqrt z)⁻¹ := by
      rw [Real.sqrt_eq_rpow, show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring,
        Real.rpow_neg hz.le, one_div]
    rw [h32, hm]
    have hcomb : 8 * (√z * z / (1 + z) ^ 2) = 8 * (√z * z) / (1 + z) ^ 2 := by ring
    rw [hcomb, le_div_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
    have hre : 2 * (√z)⁻¹ * (1 + z) ^ 2 = (√z)⁻¹ * (2 * (1 + z) ^ 2) := by ring
    rw [hre, inv_mul_le_iff₀ hs]
    nlinarith [hsq, hz1, sq_nonneg (1 + z), sq_nonneg z]
  calc |∫ r in Set.Ioi z, g r| ≤ ∫ r in Set.Ioi z, |g r| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ r in Set.Ioi z, B * (Real.sqrt r / (1 + r) ^ 2) := hstep2
    _ = B * ∫ r in Set.Ioi z, (Real.sqrt r / (1 + r) ^ 2) :=
        MeasureTheory.integral_const_mul B _
    _ ≤ B * ∫ r in Set.Ioi z, r ^ (-(3 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hstep4 hB
    _ = B * (2 * z ^ (-(1 : ℝ) / 2)) := by rw [hstep5]
    _ ≤ 8 * B * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
        have := mul_le_mul_of_nonneg_left hard hB
        nlinarith [this]

theorem L12_tail_weight {g : ℝ → ℝ} {B z : ℝ}
    (hB : 0 ≤ B) (hz : 0 < z)
    (hint : MeasureTheory.IntegrableOn g (Set.Ioi 0))
    (hbd : ∀ r : ℝ, 0 < r → |g r| ≤ B * (Real.sqrt r / (1 + r) ^ 2))
    (h0 : ∫ r in Set.Ioi 0, g r = 0) :
    |∫ r in Set.Ioi z, g r| ≤ 8 * B * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) := by
  rcases le_or_gt z 1 with hz1 | hz1
  · exact L12_tail_small hB hz hz1 hint hbd h0
  · exact L12_tail_large hB hz (le_of_lt hz1) hint hbd

end Work.FTS_RegExport.RXT.SysAux
