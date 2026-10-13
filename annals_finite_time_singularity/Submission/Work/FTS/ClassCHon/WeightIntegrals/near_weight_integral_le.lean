import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.ClassCHon.RgL2Pointwise

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.WeightIntegrals

open MeasureTheory Set

/-- **The near weight integral.**  For `0 < z` and `1 < Q`,

  `∫_{(0,z]} t^{2Q-2} / w(t)² dt ≤ z^{2Q} / (2Q-1)`,   `w(t) = (1+t)²/t²`.

The substitution `t^{2Q-2}/w(t)² = t^{2Q+2}/(1+t)⁴` (`near_pow_form`) turns the integrand into
a function that behaves like `t^{2Q-2}` for large `t` and like `t^{2Q+2}` for small `t`; the
elementary pointwise comparison

  `t^{2Q+2}/(1+t)⁴ ≤ (2Q/(2Q-1)) · t^{2Q-1}   (t > 0)`,

which only uses `t³ ≤ (1+t)⁴` and `1 ≤ 2Q/(2Q-1)`, dominates the integrand by a multiple of
`t^{2Q-1}`; integrating that over `(0,z]` gives exactly `z^{2Q}/(2Q-1)`.  No case distinction on
`z` is needed. -/
theorem near_weight_integral_le {z Q : ℝ} (hz : 0 < z) (hQ : 1 < Q) :
    ∫ t in Set.Ioc (0 : ℝ) z, t ^ (2 * Q - 2) / (Work.Spaces.w t) ^ 2
      ≤ z ^ (2 * Q) / (2 * Q - 1) := by
  have hQ1 : (0 : ℝ) < 2 * Q - 1 := by linarith
  -- The pointwise domination by a multiple of `t^{2Q-1}`.
  have hpt : ∀ t ∈ Set.Ioc (0 : ℝ) z,
      t ^ (2 * Q - 2) / (Work.Spaces.w t) ^ 2 ≤ (2 * Q / (2 * Q - 1)) * t ^ (2 * Q - 1) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    rw [Work.FTS.ClassCHon.near_pow_form ht0.le hQ]
    have h1t : (0 : ℝ) < 1 + t := by linarith
    rw [div_le_iff₀ (Real.rpow_pos_of_pos h1t 4)]
    have hc : (1 : ℝ) ≤ 2 * Q / (2 * Q - 1) := by
      rw [one_le_div (by linarith)]
      linarith
    have h3 : t ^ (3 : ℝ) ≤ (1 + t) ^ (4 : ℝ) := by
      have ha : t ^ (3 : ℝ) ≤ (1 + t) ^ (3 : ℝ) :=
        Real.rpow_le_rpow ht0.le (by linarith) (by norm_num : (0 : ℝ) ≤ 3)
      have hb : (1 + t) ^ (3 : ℝ) ≤ (1 + t) ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num : (3 : ℝ) ≤ 4)
      linarith
    have hmain : t ^ (3 : ℝ) ≤ (2 * Q / (2 * Q - 1)) * (1 + t) ^ (4 : ℝ) :=
      le_trans h3 (le_mul_of_one_le_left (Real.rpow_nonneg h1t.le 4) hc)
    calc t ^ (2 * Q + 2) = t ^ (2 * Q - 1) * t ^ (3 : ℝ) := by
          rw [← Real.rpow_add ht0, show 2 * Q - 1 + 3 = 2 * Q + 2 by ring]
      _ ≤ t ^ (2 * Q - 1) * ((2 * Q / (2 * Q - 1)) * (1 + t) ^ (4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hmain (Real.rpow_nonneg ht0.le _)
      _ = (2 * Q / (2 * Q - 1)) * t ^ (2 * Q - 1) * (1 + t) ^ (4 : ℝ) := by ring
  -- Integrability of the dominating function on `(0,z]`.
  have hbase : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (2 * Q - 1)) (Set.Ioc 0 z) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := z) (r := 2 * Q - 1)
        (by linarith : -1 < 2 * Q - 1))
  have hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => (2 * Q / (2 * Q - 1)) * t ^ (2 * Q - 1)) (Set.Ioc 0 z) :=
    hbase.const_mul _
  -- The monotone comparison of the two set integrals.
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (μ := volume.restrict (Set.Ioc (0 : ℝ) z))
    (f := fun t => t ^ (2 * Q - 2) / (Work.Spaces.w t) ^ 2)
    (g := fun t => (2 * Q / (2 * Q - 1)) * t ^ (2 * Q - 1))
    (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        exact div_nonneg (Real.rpow_nonneg ht.1.le _) (sq_nonneg _))
    hint
    (by filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
        exact hpt t ht)
  -- Evaluation of the dominating integral.
  have hIntg : ∫ t in Set.Ioc (0 : ℝ) z, (2 * Q / (2 * Q - 1)) * t ^ (2 * Q - 1)
      = z ^ (2 * Q) / (2 * Q - 1) := by
    rw [MeasureTheory.integral_const_mul,
      Work.FTS.ClassCHon.integral_Ioc_rpow_eq hz (by linarith : -1 < 2 * Q - 1)]
    rw [show 2 * Q - 1 + 1 = 2 * Q by ring]
    have h1 : (2 * Q - 1 : ℝ) ≠ 0 := by linarith
    have h2 : (2 * Q : ℝ) ≠ 0 := by linarith
    field_simp
  calc ∫ t in Set.Ioc (0 : ℝ) z, t ^ (2 * Q - 2) / (Work.Spaces.w t) ^ 2
      ≤ ∫ t in Set.Ioc (0 : ℝ) z, (2 * Q / (2 * Q - 1)) * t ^ (2 * Q - 1) := hmono
    _ = z ^ (2 * Q) / (2 * Q - 1) := hIntg

end Work.FTS.ClassCHon.WeightIntegrals
