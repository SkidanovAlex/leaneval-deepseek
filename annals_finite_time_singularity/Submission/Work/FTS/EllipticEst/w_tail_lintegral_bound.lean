import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.lintegral_Ici_ofReal_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

open MeasureTheory Set Filter

/-- The radial weight can be written `w z = (1 + 1/z)²` for `z ≠ 0`; this exhibits
`w` as a decreasing function of `z` on the positive half-line. -/
private lemma w_eq_one_add_inv_sq {z : ℝ} (hz : z ≠ 0) :
    Work.Spaces.w z = (1 + 1 / z) ^ 2 := by
  have h : (1 : ℝ) + 1 / z = (1 + z) / z := by
    rw [show (1 + z) = (1 : ℝ) + z by ring, add_div, div_self hz]
    ring
  rw [Work.Spaces.w, h, div_pow]

private lemma w_nonneg {z : ℝ} (hz : 0 < z) : 0 ≤ Work.Spaces.w z := by
  rw [w_eq_one_add_inv_sq (ne_of_gt hz)]
  positivity

private lemma w_antitoneOn : AntitoneOn Work.Spaces.w (Set.Ioi 0) := by
  intro a ha b hb hab
  rw [w_eq_one_add_inv_sq (ne_of_gt hb), w_eq_one_add_inv_sq (ne_of_gt ha)]
  have h1 : (1 : ℝ) / b ≤ 1 / a := one_div_le_one_div_of_le ha hab
  have h2 : (1 : ℝ) + 1 / b ≤ 1 + 1 / a := by linarith
  have hb0 : 0 < b := hb
  exact pow_le_pow_left₀ (by positivity) h2 2

theorem w_tail_lintegral_bound (β : ℝ) (hβ : 1 < β) {s : ℝ} (hs : 0 < s) :
    ∫⁻ z in Set.Ici s, ENNReal.ofReal ((Work.Spaces.w z) ^ 2 * z ^ (-β))
      ≤ ENNReal.ofReal ((Work.Spaces.w s) ^ 2 * s ^ (1 - β) / (β - 1)) := by
  have hws : 0 ≤ Work.Spaces.w s := w_nonneg hs
  -- Pointwise domination on `[s,∞)`: `w z ≤ w s` there, and `w s ≥ 0`.
  have hpt : ∀ᵐ z ∂(volume.restrict (Set.Ici s)),
      ENNReal.ofReal (Work.Spaces.w z ^ 2 * z ^ (-β))
        ≤ ENNReal.ofReal (Work.Spaces.w s ^ 2) * ENNReal.ofReal (z ^ (-β)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    have hz0 : 0 < z := lt_of_lt_of_le hs hz
    have hle : Work.Spaces.w z ≤ Work.Spaces.w s := w_antitoneOn hs hz0 hz
    have hsq : Work.Spaces.w z ^ 2 ≤ Work.Spaces.w s ^ 2 :=
      pow_le_pow_left₀ (w_nonneg hz0) hle 2
    have hzp : 0 ≤ z ^ (-β) := Real.rpow_nonneg (le_of_lt hz0) (-β)
    calc ENNReal.ofReal (Work.Spaces.w z ^ 2 * z ^ (-β))
        ≤ ENNReal.ofReal (Work.Spaces.w s ^ 2 * z ^ (-β)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hsq hzp)
      _ = ENNReal.ofReal (Work.Spaces.w s ^ 2) * ENNReal.ofReal (z ^ (-β)) :=
          ENNReal.ofReal_mul (pow_nonneg hws 2)
  calc ∫⁻ z in Set.Ici s, ENNReal.ofReal (Work.Spaces.w z ^ 2 * z ^ (-β))
      ≤ ∫⁻ z in Set.Ici s,
          ENNReal.ofReal (Work.Spaces.w s ^ 2) * ENNReal.ofReal (z ^ (-β)) :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal (Work.Spaces.w s ^ 2)
          * ∫⁻ z in Set.Ici s, ENNReal.ofReal (z ^ (-β)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (Work.Spaces.w s ^ 2)
          * ENNReal.ofReal (s ^ (1 - β) / (β - 1)) := by
        rw [Work.Elliptic.lintegral_Ici_ofReal_rpow hβ hs]
    _ = ENNReal.ofReal (Work.Spaces.w s ^ 2 * (s ^ (1 - β) / (β - 1))) :=
        (ENNReal.ofReal_mul (pow_nonneg hws 2)).symm
    _ = ENNReal.ofReal (Work.Spaces.w s ^ 2 * s ^ (1 - β) / (β - 1)) := by
        rw [mul_div_assoc]

end Work.FTS.EllipticEst
