import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.EllExist.RadGreenDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.ClassC

/-- **The tail primitive decays like `z^{-p-1}`.**

`rgB α m c z = ∫_t∈(z,∞) c t · t^{-p-1}` with `p = rgP α m = 2m/α`, and the decay hypothesis
`|c t| ≤ K/t` for `t ≥ 1` makes the tail integrand dominated by `K · t^{-p-2}`, whose integral
over `(z,∞)` is exactly `K · z^{-p-1}/(p+1)` (the exponent `-p-2 < -1` because `p ≥ 0`).

No measurability of `c` is needed: if `rgF2` is not a.e. strongly measurable Mathlib's junk
integral vanishes and the bound is trivial, while in the measurable case the majorant
`K · t^{-p-2}` is integrable on `(z,∞)` for `z > 0` by `integrableOn_Ioi_rpow_of_lt`. -/
private lemma rgB_abs_le {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ} {K : ℝ}
    (hK : ∀ t : ℝ, 1 ≤ t → |c t| ≤ K / t) {z : ℝ} (hz : 1 ≤ z) :
    |Work.FTS.EllExist.rgB α m c z|
      ≤ K * z ^ (-(Work.FTS.EllExist.rgP α m) - 1) / (Work.FTS.EllExist.rgP α m + 1) := by
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
  have hp0 : 0 ≤ Work.FTS.EllExist.rgP α m := Work.FTS.EllExist.rgP_nonneg hα m
  have hlt : -(Work.FTS.EllExist.rgP α m) - 2 < (-1 : ℝ) := by linarith
  -- triangle inequality for the Bochner integral
  have hstep1 : |Work.FTS.EllExist.rgB α m c z|
      ≤ ∫ t in Set.Ioi z, ‖Work.FTS.EllExist.rgF2 α m c t‖ := by
    have h := norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioi z))
      (Work.FTS.EllExist.rgF2 α m c)
    rw [Work.FTS.EllExist.rgB]
    simpa only [Real.norm_eq_abs] using h
  -- the pointwise domination of the tail integrand by the majorant
  have hpoint : ∀ᵐ t ∂(volume.restrict (Set.Ioi z)), ‖Work.FTS.EllExist.rgF2 α m c t‖
      ≤ K * t ^ (-(Work.FTS.EllExist.rgP α m) - 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hz0 ht
    have ht1 : 1 ≤ t := le_trans hz (le_of_lt ht)
    have hc : |c t| ≤ K / t := hK t ht1
    have hpow : 0 < t ^ (-(Work.FTS.EllExist.rgP α m) - 1) := Real.rpow_pos_of_pos ht0 _
    rw [Work.FTS.EllExist.rgF2, Real.norm_eq_abs, abs_mul, abs_of_pos hpow]
    calc |c t| * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)
        ≤ (K / t) * t ^ (-(Work.FTS.EllExist.rgP α m) - 1) :=
          mul_le_mul_of_nonneg_right hc (le_of_lt hpow)
      _ = K * t ^ (-(Work.FTS.EllExist.rgP α m) - 2) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg_one t,
            show K * t ^ (-1 : ℝ) * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)
              = K * (t ^ (-1 : ℝ) * t ^ (-(Work.FTS.EllExist.rgP α m) - 1)) from by ring,
            ← Real.rpow_add ht0,
            show (-1 : ℝ) + (-(Work.FTS.EllExist.rgP α m) - 1)
              = -(Work.FTS.EllExist.rgP α m) - 2 from by ring]
  -- the majorant is integrable on `(z,∞)`
  have hint : Integrable (fun t => K * t ^ (-(Work.FTS.EllExist.rgP α m) - 2))
      (volume.restrict (Set.Ioi z)) :=
    (integrableOn_Ioi_rpow_of_lt hlt hz0).const_mul K
  have hstep2 : ∫ t in Set.Ioi z, ‖Work.FTS.EllExist.rgF2 α m c t‖
      ≤ ∫ t in Set.Ioi z, K * t ^ (-(Work.FTS.EllExist.rgP α m) - 2) :=
    integral_mono_of_nonneg (Eventually.of_forall (fun t => norm_nonneg _)) hint hpoint
  -- the value of the majorant integral
  have hval : ∫ t in Set.Ioi z, K * t ^ (-(Work.FTS.EllExist.rgP α m) - 2)
      = K * z ^ (-(Work.FTS.EllExist.rgP α m) - 1) / (Work.FTS.EllExist.rgP α m + 1) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt hz0,
      show -(Work.FTS.EllExist.rgP α m) - 2 + 1 = -(Work.FTS.EllExist.rgP α m) - 1 from by ring,
      show -(Work.FTS.EllExist.rgP α m) - 1 = -(Work.FTS.EllExist.rgP α m + 1) from by ring,
      neg_div_neg_eq]
    ring
  calc |Work.FTS.EllExist.rgB α m c z|
      ≤ ∫ t in Set.Ioi z, ‖Work.FTS.EllExist.rgF2 α m c t‖ := hstep1
    _ ≤ ∫ t in Set.Ioi z, K * t ^ (-(Work.FTS.EllExist.rgP α m) - 2) := hstep2
    _ = K * z ^ (-(Work.FTS.EllExist.rgP α m) - 1) / (Work.FTS.EllExist.rgP α m + 1) := hval

theorem rgB_far_bound {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) {c : ℝ → ℝ}
    (hdec : ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 1 ≤ t → |c t| ≤ K / t)
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∃ C2 : ℝ, 0 ≤ C2 ∧ ∀ z : ℝ, 1 ≤ z →
      z ^ (Work.FTS.EllExist.rgP α m) * |Work.FTS.EllExist.rgB α m c z| ≤ C2 / z := by
  obtain ⟨K, hKpos, hK⟩ := hdec
  have hp1 : 0 < Work.FTS.EllExist.rgP α m + 1 := by
    have := Work.FTS.EllExist.rgP_nonneg hα m
    linarith
  refine ⟨K / (Work.FTS.EllExist.rgP α m + 1),
    div_nonneg (le_of_lt hKpos) (le_of_lt hp1), fun z hz => ?_⟩
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
  have hzp : 0 < z ^ (Work.FTS.EllExist.rgP α m) := Real.rpow_pos_of_pos hz0 _
  have hmul : z ^ (Work.FTS.EllExist.rgP α m) * |Work.FTS.EllExist.rgB α m c z|
      ≤ z ^ (Work.FTS.EllExist.rgP α m)
        * (K * z ^ (-(Work.FTS.EllExist.rgP α m) - 1)
            / (Work.FTS.EllExist.rgP α m + 1)) :=
    mul_le_mul_of_nonneg_left (rgB_abs_le hα m hK hz) (le_of_lt hzp)
  calc z ^ (Work.FTS.EllExist.rgP α m) * |Work.FTS.EllExist.rgB α m c z|
      ≤ z ^ (Work.FTS.EllExist.rgP α m)
        * (K * z ^ (-(Work.FTS.EllExist.rgP α m) - 1)
            / (Work.FTS.EllExist.rgP α m + 1)) := hmul
    _ = K / (Work.FTS.EllExist.rgP α m + 1) / z := by
        rw [show z ^ (Work.FTS.EllExist.rgP α m)
              * (K * z ^ (-(Work.FTS.EllExist.rgP α m) - 1)
                  / (Work.FTS.EllExist.rgP α m + 1))
            = K * (z ^ (Work.FTS.EllExist.rgP α m)
                * z ^ (-(Work.FTS.EllExist.rgP α m) - 1))
              / (Work.FTS.EllExist.rgP α m + 1) from by ring,
          ← Real.rpow_add hz0,
          show Work.FTS.EllExist.rgP α m + (-(Work.FTS.EllExist.rgP α m) - 1) = -1 from by ring,
          Real.rpow_neg_one]
        ring

end Work.FTS.ClassC
