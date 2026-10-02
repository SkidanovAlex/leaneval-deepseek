import Mathlib
import Submission.Work.Implosion.Ecalle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Écalle coordinate is `1/ζ` to second order

For the Écalle coordinate `u(ζ) = log((ζ+a)/(ζ−a))/(2a)` of `Ecalle.lean` we show that,
whenever `‖ζ‖ ≥ 1` and `4‖a‖ ≤ ‖ζ‖`,

  `‖ecalCoord a ζ − 1/ζ‖ ≤ (4/9)·‖a‖²/‖ζ‖²`.

This is the quantitative form of the fact that the Écalle coordinate is asymptotic to
`1/ζ` near infinity along the direction of `a`: with `w = a/ζ` (so `‖w‖ ≤ 1/4`),

  `ecalCoord a ζ = (1/a)·artanh w`,  `1/ζ = w/a`,

and the second-order term of `2·artanh w = log((1+w)/(1−w))` cancels, leaving a cubic
remainder.  The estimate is obtained from Mathlib's second-order bounds for the complex
logarithm (`Complex.norm_log_sub_logTaylor_le`) applied to `log (1+w)` and to
`log (1−w)⁻¹`; the leading `± w²/2` terms cancel.
-/

namespace Work.Implosion.Approx

open Complex

/-- `logTaylor 3 z = z - z²/2`, the Taylor polynomial of `log (1+z)` up to degree `2`. -/
private lemma ecal_logTaylor_three :
    Complex.logTaylor 3 = fun z : ℂ => z - z ^ 2 / 2 := by
  funext z
  simp only [Complex.logTaylor_succ, Complex.logTaylor_zero, Pi.add_apply]
  ring

/-- Splitting the branch of the logarithm: for `‖w‖ < 1` the number `(1+w)/(1-w)` has
argument in `(-π, π)`, so its logarithm is the sum of the logarithms of `1+w` and
`(1-w)⁻¹`. -/
private lemma ecal_log_ratio_eq (w : ℂ) (hw : ‖w‖ < 1) :
    Complex.log ((1 + w) / (1 - w)) = Complex.log (1 + w) + Complex.log ((1 - w)⁻¹) := by
  have hb1 : (1 : ℝ) - ‖w‖ ≤ ‖(1 : ℂ) + w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-w)
    rw [norm_neg, norm_one, sub_neg_eq_add] at h
    exact h
  have hb2 : (1 : ℝ) - ‖w‖ ≤ ‖(1 : ℂ) - w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) w
    rw [norm_one] at h
    exact h
  have h1w : (1 + w) ≠ 0 := by
    intro h
    have : ‖(1 : ℂ) + w‖ = 0 := by rw [h, norm_zero]
    have := norm_nonneg w
    linarith
  have h2w : (1 - w) ≠ 0 := by
    intro h
    have : ‖(1 : ℂ) - w‖ = 0 := by rw [h, norm_zero]
    have := norm_nonneg w
    linarith
  have ha1 : (1 + w).arg ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    Complex.arg_one_add_mem_Ioo hw
  have ha2 : (1 - w).arg ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    Complex.arg_one_add_mem_Ioo (z := -w) (by simpa using hw)
  have hne : (1 - w).arg ≠ Real.pi := by
    intro h
    have h' := ha2
    rw [Set.mem_Ioo] at h'
    linarith [h'.2, Real.pi_pos]
  have hinv : ((1 - w)⁻¹).arg = -((1 - w).arg) := by
    rw [Complex.arg_inv, ite_eq_right hne]
  have hsum : (1 + w).arg + ((1 - w)⁻¹).arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [hinv, Set.mem_Ioc]
    have h1 := ha1
    rw [Set.mem_Ioo] at h1
    have h2 := ha2
    rw [Set.mem_Ioo] at h2
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  rw [div_eq_mul_inv]
  exact Complex.log_mul h1w (inv_ne_zero h2w) hsum

/-- The cubic remainder of `log ((1+w)/(1-w))`: for `‖w‖ ≤ 1/4` one has
`‖log ((1+w)/(1-w)) − 2w‖ ≤ (8/9)·‖w‖³`. -/
private lemma ecal_norm_log_ratio_sub_two_mul_le (w : ℂ) (hw : ‖w‖ ≤ 1 / 4) :
    ‖Complex.log ((1 + w) / (1 - w)) - 2 * w‖ ≤ 8 / 9 * ‖w‖ ^ 3 := by
  have hw1 : ‖w‖ < 1 := by linarith
  have hsplit := ecal_log_ratio_eq w hw1
  have hA : ‖Complex.log (1 + w) - (w - w ^ 2 / 2)‖ ≤ ‖w‖ ^ 3 * (1 - ‖w‖)⁻¹ / 3 := by
    have h := Complex.norm_log_sub_logTaylor_le 2 hw1
    rw [ecal_logTaylor_three] at h
    have h2 : ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
    rw [h2] at h
    exact h
  have hB : ‖Complex.log (1 - w)⁻¹ - (w + w ^ 2 / 2)‖ ≤ ‖w‖ ^ 3 * (1 - ‖w‖)⁻¹ / 3 := by
    have h := Complex.norm_log_one_sub_inv_add_logTaylor_neg_le 2 hw1
    have heq : Complex.log (1 - w)⁻¹ + Complex.logTaylor 3 (-w)
        = Complex.log (1 - w)⁻¹ - (w + w ^ 2 / 2) := by
      simp only [ecal_logTaylor_three]
      ring
    rw [heq] at h
    have h2 : ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
    rw [h2] at h
    exact h
  have hinv : (1 - ‖w‖)⁻¹ ≤ 4 / 3 := by
    rw [inv_le_comm₀ (by linarith : (0 : ℝ) < 1 - ‖w‖) (by norm_num : (0 : ℝ) < 4 / 3)]
    norm_num
    linarith
  rw [hsplit]
  have hkey : Complex.log (1 + w) + Complex.log ((1 - w)⁻¹) - 2 * w
      = (Complex.log (1 + w) - (w - w ^ 2 / 2))
        + (Complex.log (1 - w)⁻¹ - (w + w ^ 2 / 2)) := by
    ring
  rw [hkey]
  calc ‖(Complex.log (1 + w) - (w - w ^ 2 / 2))
          + (Complex.log (1 - w)⁻¹ - (w + w ^ 2 / 2))‖
      ≤ ‖Complex.log (1 + w) - (w - w ^ 2 / 2)‖
        + ‖Complex.log (1 - w)⁻¹ - (w + w ^ 2 / 2)‖ := norm_add_le _ _
    _ ≤ ‖w‖ ^ 3 * (1 - ‖w‖)⁻¹ / 3 + ‖w‖ ^ 3 * (1 - ‖w‖)⁻¹ / 3 := add_le_add hA hB
    _ = 2 / 3 * (‖w‖ ^ 3 * (1 - ‖w‖)⁻¹) := by ring
    _ ≤ 2 / 3 * (‖w‖ ^ 3 * (4 / 3)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 8 / 9 * ‖w‖ ^ 3 := by ring

theorem ecalCoord_sub_inv_le (a ζ : ℂ) (ha : a ≠ 0) (hζ : 1 ≤ ‖ζ‖) (haζ : 4 * ‖a‖ ≤ ‖ζ‖) :
    ‖ecalCoord a ζ - 1 / ζ‖ ≤ 4 / 9 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by
  have hζpos : 0 < ‖ζ‖ := lt_of_lt_of_le zero_lt_one hζ
  have hζne : ζ ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hζpos)
  have hanorm : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set w : ℂ := a / ζ with hw
  have hwnorm : ‖w‖ = ‖a‖ / ‖ζ‖ := by rw [hw, norm_div]
  have hwq : ‖w‖ ≤ 1 / 4 := by
    rw [hwnorm, div_le_iff₀ hζpos]
    linarith
  -- the Möbius coordinate is `(1+w)/(1-w)` with `w = a/ζ`
  have hmob : mobius a ζ = (1 + w) / (1 - w) := by
    have h1 : 1 + w = (ζ + a) / ζ := by rw [hw, add_div, div_self hζne]
    have h2 : 1 - w = (ζ - a) / ζ := by rw [hw, sub_div, div_self hζne]
    rw [mobius, h1, h2, ← div_div_div_cancel_right₀ hζne (ζ + a) (ζ - a)]
  -- `ecalCoord a ζ - 1/ζ = (log ((1+w)/(1-w)) - 2w)/(2a)`
  have hcancel : ecalCoord a ζ - 1 / ζ
      = (Complex.log (mobius a ζ) - 2 * w) / (2 * a) := by
    rw [ecalCoord, hw]
    field_simp
  rw [hcancel, hmob, norm_div, norm_mul, Complex.norm_ofNat]
  have hb := ecal_norm_log_ratio_sub_two_mul_le w hwq
  calc ‖Complex.log ((1 + w) / (1 - w)) - 2 * w‖ / (2 * ‖a‖)
      ≤ (8 / 9 * ‖w‖ ^ 3) / (2 * ‖a‖) := div_le_div_of_nonneg_right hb (by positivity)
    _ = 4 / 9 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 := by
        rw [hwnorm]
        field_simp
        ring
    _ ≤ 4 / 9 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by
        have hpow : ‖ζ‖ ^ 2 ≤ ‖ζ‖ ^ 3 := by nlinarith [hζ, sq_nonneg (‖ζ‖)]
        have h1 : 1 / ‖ζ‖ ^ 3 ≤ 1 / ‖ζ‖ ^ 2 := one_div_le_one_div_of_le (by positivity) hpow
        calc 4 / 9 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 = (4 / 9 * ‖a‖ ^ 2) * (1 / ‖ζ‖ ^ 3) := by ring
          _ ≤ (4 / 9 * ‖a‖ ^ 2) * (1 / ‖ζ‖ ^ 2) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = 4 / 9 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by ring

end Work.Implosion.Approx
