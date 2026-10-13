import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.EllExist.Honesty.RadGreenDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.EllExist.Honesty

/-- Far-field bound for a general `z^s`-weighted tail integral: if `0 ≤ s`, `c` is continuous
on `(0,∞)` and `|c t| ≤ M t^{-s-2}` for `t ≥ 1`, then for `z > 1` the weighted tail integral
`z^s ∫_z^∞ c t t^{-s-1} dt` is bounded by `M z^{-s-2}/(2s+2)`.  The exponent `-2s-3` of the
dominating function is `< -1`, so the integral converges and can be computed explicitly. -/
lemma G2_far_bound_aux (s M : ℝ) (hs : 0 ≤ s) (_hM : 0 ≤ M) {c : ℝ → ℝ}
    (_hc : ContinuousOn c (Set.Ioi 0))
    (hdec : ∀ t, 1 ≤ t → |c t| ≤ M * t ^ (-s - 2)) :
    ∀ z ∈ Set.Ioi 1, |z ^ s * (∫ t in Set.Ioi z, c t * t ^ (-s - 1))|
      ≤ M / (2 * s + 2) * z ^ (-s - 2) := by
  intro z hz
  have hz0 : 0 < z := lt_trans one_pos hz
  have hz1 : 1 ≤ z := le_of_lt hz
  -- the dominating exponent is `< -1`, hence the dominating function is integrable
  have hexp : -2 * s - 3 < -1 := by linarith
  have hdom : Integrable (fun t : ℝ => M * t ^ (-2 * s - 3)) (volume.restrict (Set.Ioi z)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -2 * s - 3) hexp hz0).const_mul M
  -- pointwise domination of the integrand
  have hpt : ∀ t ∈ Set.Ioi z, ‖c t * t ^ (-s - 1)‖ ≤ M * t ^ (-2 * s - 3) := by
    intro t ht
    have ht1 : 1 ≤ t := le_trans hz1 (le_of_lt ht)
    have ht0 : 0 < t := lt_of_lt_of_le one_pos ht1
    have hpow : 0 < t ^ (-s - 1) := Real.rpow_pos_of_pos ht0 _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpow]
    calc |c t| * t ^ (-s - 1)
        ≤ (M * t ^ (-s - 2)) * t ^ (-s - 1) :=
          mul_le_mul_of_nonneg_right (hdec t ht1) (le_of_lt hpow)
      _ = M * t ^ (-2 * s - 3) := by
          rw [mul_assoc, ← Real.rpow_add ht0,
            show (-s - 2) + (-s - 1) = -2 * s - 3 from by ring]
  -- monotonicity of the integral
  have hmono : (∫ t in Set.Ioi z, ‖c t * t ^ (-s - 1)‖)
      ≤ ∫ t in Set.Ioi z, M * t ^ (-2 * s - 3) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t => norm_nonneg _) hdom ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact hpt t ht
  -- the value of the dominating integral
  have hnegdiv : ∀ x y : ℝ, -x / y = x / (-y) := by intro x y; ring
  have hinner : -z ^ (-2 * s - 2) / (-2 * s - 2) = z ^ (-2 * s - 2) / (2 * s + 2) := by
    calc -z ^ (-2 * s - 2) / (-2 * s - 2)
        = z ^ (-2 * s - 2) / (-(-2 * s - 2)) := hnegdiv _ _
      _ = z ^ (-2 * s - 2) / (2 * s + 2) := by congr 1; ring
  have hint : ∫ t in Set.Ioi z, M * t ^ (-2 * s - 3)
      = M * (z ^ (-2 * s - 2) / (2 * s + 2)) := by
    rw [MeasureTheory.integral_const_mul]
    have hbase : ∫ t in Set.Ioi z, t ^ (-2 * s - 3) = -z ^ (-2 * s - 2) / (-2 * s - 2) := by
      have h := integral_Ioi_rpow_of_lt (a := -2 * s - 3) hexp hz0
      rw [show (-2 * s - 3 + 1 : ℝ) = -2 * s - 2 from by ring] at h
      exact h
    rw [hbase, hinner]
  have hmain : ‖∫ t in Set.Ioi z, c t * t ^ (-s - 1)‖
      ≤ M * (z ^ (-2 * s - 2) / (2 * s + 2)) :=
    le_trans (MeasureTheory.norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Ioi z)) (fun t : ℝ => c t * t ^ (-s - 1)))
      (le_trans hmono (le_of_eq hint))
  -- reassemble the weight `z^s`
  have hp : z ^ s * z ^ (-2 * s - 2) = z ^ (-s - 2) := by
    rw [← Real.rpow_add hz0]; congr 1; ring
  calc |z ^ s * (∫ t in Set.Ioi z, c t * t ^ (-s - 1))|
      = z ^ s * ‖∫ t in Set.Ioi z, c t * t ^ (-s - 1)‖ := by
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hz0 s), Real.norm_eq_abs]
    _ ≤ z ^ s * (M * (z ^ (-2 * s - 2) / (2 * s + 2))) :=
        mul_le_mul_of_nonneg_left hmain (le_of_lt (Real.rpow_pos_of_pos hz0 s))
    _ = M / (2 * s + 2) * z ^ (-s - 2) := by
        calc z ^ s * (M * (z ^ (-2 * s - 2) / (2 * s + 2)))
            = M / (2 * s + 2) * (z ^ s * z ^ (-2 * s - 2)) := by ring
          _ = M / (2 * s + 2) * z ^ (-s - 2) := by rw [hp]

-- Far-field pointwise bound for the `z^{s⁺}` Green term `G2 α m c` (`s⁺ = 2m/α`) of
-- `Work.FTS.EllExist.Honesty.G2`, defined as
-- `G2 α m c z = z ^ (2*(m:ℝ)/α) * ∫ t in Set.Ioi z, c t * t ^ (-(2*(m:ℝ)/α) - 1)`.
-- Route: for `z ≥ 1` (so `z > 0` and every `t ∈ Ioi z` satisfies `t ≥ 1`), dominate the
-- integrand by `M * t ^ (-2*(2*(m:ℝ)/α) - 3)` with `hdec`, use `integrableOn_Ioi_rpow_of_lt`
-- (the exponent is `< -1`) plus `Integrable.mono'` for integrability, then
-- `MeasureTheory.norm_integral_le_integral_norm` and `integral_Ioi_rpow_of_lt` to get
-- `|∫| ≤ M * z ^ (-2*(2*(m:ℝ)/α) - 2) / (2*(2*(m:ℝ)/α) + 2)`, and finally
-- `Real.rpow_add` to turn `z ^ (2*(m:ℝ)/α) * z ^ (-2*(2*(m:ℝ)/α) - 2)` into
-- `z ^ (-(2*(m:ℝ)/α) - 2)`.
theorem G2_far_bound (α : ℝ) (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} (M : ℝ) (hM : 0 ≤ M)
    (hc : ContinuousOn c (Set.Ioi 0))
    (hdec : ∀ t, 1 ≤ t → |c t| ≤ M * t ^ (-(2 * (m : ℝ) / α) - 2)) :
    ∀ z ∈ Set.Ioi 1, |Work.FTS.EllExist.Honesty.G2 α m c z|
      ≤ M / (2 * (2 * (m : ℝ) / α) + 2) * z ^ (-(2 * (m : ℝ) / α) - 2) := by
  have hs : 0 ≤ 2 * (m : ℝ) / α := by
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    positivity
  have h := G2_far_bound_aux (2 * (m : ℝ) / α) M hs hM hc hdec
  simpa only [G2] using h

end Work.FTS.EllExist.Honesty
