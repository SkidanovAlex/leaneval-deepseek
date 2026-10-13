/-
# `Work.FTS.PhiStar.Honesty.rgB_tail_far_le` — the *far* piece of the tail bound for `rgB`

This is the `(1,∞)` half of the splitting of `∫_δ^∞ ‖c t · t^{-p-1}‖` used for the far-field
(`z → ∞`) weighted `L²`-honesty of the radial Green function of `Work.FTS.PhiStar`.

**Statement.**  If `∫_1^∞ (c t)² dt < ∞` and `p ≥ 2`, then
`∫_1^∞ ‖c t · t^{-p-1}‖ dt ≤ (∫_1^∞ (c t)² dt)/2 + 1`.

**Proof.**  Purely elementary: on `(1,∞)` one has `t^{-p-1} ≤ t^{-3}` (as `p ≥ 2`), so the
integrand is dominated pointwise by `|c t| · t^{-3}`, and AM–GM
(`|ab| ≤ (a² + b²)/2`, i.e. `(a-b)² ≥ 0`) gives

  `|c t| · t^{-3} ≤ (|c t|² + (t^{-3})²)/2 = (1/2)(c t)² + (1/2) t^{-6}`,

a combination of the two integrable functions `c²` (hypothesis) and `t^{-6}`
(`-6 < -1`).  Monotonicity of the Bochner integral (`integral_mono_of_nonneg`, which needs no
measurability of the integrand: in the non-a.e.-strongly-measurable case the Bochner integral is
junk `0` while the majorant is nonnegative) then yields the bound, and the remaining tail
integral is evaluated with `integral_Ioi_rpow_of_lt`: `∫_1^∞ t^{-6} = 1/5`, so that the excess is
`(1/2)·(1/5) = 1/10 ≤ 1`.

Note that `c` itself is *not* assumed measurable; no measurability of `c` is needed, since the
majorant is built from `c²` (measurable by the hypothesis) and the explicit power `t^{-6}`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

theorem rgB_tail_far_le {c : ℝ → ℝ} {p : ℝ} (hp : 2 ≤ p)
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∫ t in Set.Ioi 1, ‖c t * t ^ (-p - 1)‖ ≤ (∫ x in Set.Ioi (1 : ℝ), (c x) ^ 2) / 2 + 1 := by
  -- the two ingredients of the majorant
  have htail : ∫ t in Ioi (1 : ℝ), t ^ (-6 : ℝ) = 1 / 5 := by
    rw [integral_Ioi_rpow_of_lt (a := (-6 : ℝ)) (c := 1) (by norm_num) (by norm_num)]
    norm_num
  have hpow : IntegrableOn (fun t : ℝ => t ^ (-6 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (a := (-6 : ℝ)) (c := 1) (by norm_num) (by norm_num)
  have hmaj : IntegrableOn (fun t : ℝ => (1 / 2 : ℝ) * (c t) ^ 2 + (1 / 2 : ℝ) * t ^ (-6 : ℝ))
      (Ioi 1) := (hfar.const_mul (1 / 2)).add (hpow.const_mul (1 / 2))
  -- the pointwise domination on `(1,∞)`
  have hle : (fun t : ℝ => ‖c t * t ^ (-p - 1)‖) ≤ᵐ[volume.restrict (Ioi 1)]
      (fun t : ℝ => (1 / 2 : ℝ) * (c t) ^ 2 + (1 / 2 : ℝ) * t ^ (-6 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := lt_trans one_pos ht1
    have hpe : t ^ (-p - 1) ≤ t ^ (-3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
    have h1 : ‖c t * t ^ (-p - 1)‖ = |c t| * t ^ (-p - 1) := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    rw [h1]
    calc |c t| * t ^ (-p - 1) ≤ |c t| * t ^ (-3 : ℝ) :=
          mul_le_mul_of_nonneg_left hpe (abs_nonneg _)
      _ ≤ (|c t| ^ 2 + (t ^ (-3 : ℝ)) ^ 2) / 2 := by
          nlinarith [sq_nonneg (|c t| - t ^ (-3 : ℝ))]
      _ = (1 / 2 : ℝ) * (c t) ^ 2 + (1 / 2 : ℝ) * t ^ (-6 : ℝ) := by
          have hsq : (t ^ (-3 : ℝ)) ^ 2 = t ^ (-6 : ℝ) := by
            rw [sq, ← Real.rpow_add ht0]; norm_num
          rw [sq_abs, hsq]; ring
  -- the value of the majorant integral
  have hval : ∫ t in Ioi (1 : ℝ), ((1 / 2 : ℝ) * (c t) ^ 2 + (1 / 2 : ℝ) * t ^ (-6 : ℝ))
      = (1 / 2 : ℝ) * (∫ x in Ioi (1 : ℝ), (c x) ^ 2) + (1 / 2 : ℝ) * (1 / 5) := by
    rw [integral_add (hfar.const_mul (1 / 2)) (hpow.const_mul (1 / 2)), integral_const_mul,
      integral_const_mul, htail]
  -- monotonicity of the integral
  have hmono := integral_mono_of_nonneg (μ := volume.restrict (Ioi 1))
    (f := fun t : ℝ => ‖c t * t ^ (-p - 1)‖)
    (g := fun t : ℝ => (1 / 2 : ℝ) * (c t) ^ 2 + (1 / 2 : ℝ) * t ^ (-6 : ℝ))
    (Eventually.of_forall fun t => norm_nonneg _) hmaj hle
  rw [hval] at hmono
  linarith

end Work.FTS.PhiStar.Honesty
