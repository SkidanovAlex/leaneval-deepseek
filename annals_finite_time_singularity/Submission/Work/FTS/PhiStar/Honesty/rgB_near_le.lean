import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem rgB_near_le {c : ℝ → ℝ} {p ε z δ : ℝ} (hp : 3 / 2 < p) (hε : 0 ≤ ε) (hz : 0 < z)
    (hzδ : z ≤ δ)
    (hvy : ∀ t : ℝ, 0 < t → t ≤ δ → |c t| ≤ ε * t ^ ((3 : ℝ) / 2)) :
    ∫ t in Set.Ioc z δ, ‖c t * t ^ (-p - 1)‖ ≤ ε * z ^ (3 / 2 - p) / (p - 3 / 2) := by
  -- `z > 0` and `p > 3/2`; the exponent of the majorant is `1/2 - p < -1`, so that the
  -- primitive `t^{3/2-p}/(3/2-p)` is *negative* and increasing, which is what the comparison
  -- `δ^{3/2-p} ≤ z^{3/2-p}` for `δ ≥ z` encodes.
  have hp32 : 0 < p - 3 / 2 := by linarith
  have hδ : 0 < δ := lt_of_lt_of_le hz hzδ
  -- pointwise domination of the integrand: `|c t| t^{-p-1} ≤ ε t^{3/2} t^{-p-1} = ε t^{1/2-p}`
  have hpt : ∀ t ∈ Set.Ioc z δ, ‖c t * t ^ (-p - 1)‖ ≤ ε * t ^ ((1:ℝ)/2 - p) := by
    intro t ht
    obtain ⟨hzt, htδ⟩ := ht
    have ht0 : 0 < t := lt_trans hz hzt
    have hp1 : 0 < t ^ (-p - 1) := Real.rpow_pos_of_pos ht0 _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp1]
    calc |c t| * t ^ (-p - 1)
        ≤ (ε * t ^ ((3:ℝ)/2)) * t ^ (-p - 1) :=
          mul_le_mul_of_nonneg_right (hvy t ht0 htδ) hp1.le
      _ = ε * t ^ ((1:ℝ)/2 - p) := by
          rw [show ε * t ^ ((3:ℝ)/2) * t ^ (-p - 1)
                = ε * (t ^ ((3:ℝ)/2) * t ^ (-p - 1)) from by ring,
              ← Real.rpow_add ht0,
              show (3:ℝ)/2 + (-p - 1) = (1:ℝ)/2 - p from by ring]
  -- the majorant is integrable on `Ioc z δ` (it is continuous on the compact `Icc z δ`)
  have hcont : ContinuousOn (fun t : ℝ => ε * t ^ ((1:ℝ)/2 - p)) (Set.Icc z δ) :=
    continuousOn_const.mul
      (ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (by linarith [hx.1] : x ≠ 0)))
  have hint : MeasureTheory.IntegrableOn (fun t : ℝ => ε * t ^ ((1:ℝ)/2 - p)) (Set.Ioc z δ) :=
    (hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioc z δ)),
      ‖c t * t ^ (-p - 1)‖ ≤ ε * t ^ ((1:ℝ)/2 - p) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hpt)
  -- monotonicity of the integral of a nonnegative function under a pointwise bound
  have hmono : ∫ t in Set.Ioc z δ, ‖c t * t ^ (-p - 1)‖
      ≤ ∫ t in Set.Ioc z δ, ε * t ^ ((1:ℝ)/2 - p) :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hint hae
  -- the explicit value of the majorant integral, via the primitive of `t^{1/2-p}`
  have hint2 : ∫ t in Set.Ioc z δ, t ^ ((1:ℝ)/2 - p)
      = (z ^ (3/2 - p) - δ ^ (3/2 - p)) / (p - 3/2) := by
    rw [← intervalIntegral.integral_of_le hzδ]
    rw [integral_rpow (a := z) (b := δ) (r := (1:ℝ)/2 - p) (Or.inr ⟨by intro h; linarith, by
      rw [Set.uIcc_of_le hzδ]
      exact fun h => absurd h.1 (not_le_of_gt hz)⟩),
      show (1:ℝ)/2 - p + 1 = (3:ℝ)/2 - p from by ring,
      show ((3:ℝ)/2 - p : ℝ) = -(p - 3/2) from by ring,
      div_neg, ← neg_div, neg_sub]
  have hval : ∫ t in Set.Ioc z δ, ε * t ^ ((1:ℝ)/2 - p)
      = ε * ((z ^ (3/2 - p) - δ ^ (3/2 - p)) / (p - 3/2)) := by
    rw [MeasureTheory.integral_const_mul, hint2]
  -- `δ^{3/2-p} ≥ 0`, so dropping it can only increase the value
  have hfinal : ε * ((z ^ (3/2 - p) - δ ^ (3/2 - p)) / (p - 3/2))
      ≤ ε * z ^ (3/2 - p) / (p - 3/2) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hp32.le
    nlinarith [Real.rpow_nonneg hδ.le (3/2 - p), hε]
  exact le_trans hmono (le_trans (le_of_eq hval) hfinal)

end Work.FTS.PhiStar.Honesty
