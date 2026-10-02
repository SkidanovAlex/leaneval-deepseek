/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.approxEcal_end_in_small` — the incoming end at *small* `‖ζ‖`

The delivered Implosion asymptotics for the incoming end,
`Work.Implosion.Approx.approxEcal_end_in`, is stated in the regime `‖ζ‖ ≥ 1`, `λ ≤ 1`, and with
the (coarser) error `O(λ²/‖ζ‖²)`.  The MATCH comparison of `Work.PARIMPL2.MatchCore` lives on a
window at `‖chartZeta‖ ≈ 1/R < 1`, so the asymptotics is needed in the *small*-`‖ζ‖` form
(`Submission/Work/PARIMPL2/NOTES.md` §6; `MatchCore.lean`'s header): the regime is
`ζ.re < 0`, `‖ζ‖ ≤ 4`, `4λ ≤ ‖ζ‖`, and the error is the *sharp* one `O(λ²/‖ζ‖³)`.

This statement is **homogeneous** in the scaling `ζ ↦ tζ`, `a ↦ ta` — the error term
`λ²/‖ζ‖³` is of degree `-1`, exactly like the leading correction — so it is not a
consequence of the `‖ζ‖ ≥ 1` statement, but the very same proof goes through with the
sharp exponent; the hypothesis `‖ζ‖ ≤ 4` is what converts the sub-leading
`O(λ²/‖ζ‖²)` contribution of `log (cosh (a·u))` into `O(λ²/‖ζ‖³)`.

The proof is the proof of `approxEcal_end_in`, with two changes:

* the Écalle-coordinate expansion retains its cubic remainder
  (`ecalCoord_sub_inv_le_small`, from `Work.Implosion.Approx.ecalCoord_sub_inv_le`);
* hence no lower bound on `‖ζ‖` is needed, and the constant is `4/9 + 24K`.

Everything else is verbatim: `ecalPt_ecalCoord`, the cotangent identity
`Ecalle.ecallePt_eq_coth`, the branch condition `(sinh (a·u)/a).im < 0` (which the shift
identity `Approx.approxEcal_shift` converts into the additive `πi/a + πiκ`), and the
logarithmic identity `log (sinh (a·u)/a) + log ζ = log (cosh (a·u))`, which needs
`Im ζ > 0` (derived here as `im_pos_of_sinh_im_neg_small` from
`Approx.ecalPt_im_pos_of_sinh_im_neg`).
-/
import Mathlib
import Submission.Work.PARIMPL2.MatchCore
import Submission.Work.Implosion.Approx.ecalCoord_sub_inv_le
import Submission.Work.Implosion.Approx.ecalPt_im_pos_of_sinh_im_neg
import Submission.Work.Implosion.Approx.approxEcal_shift
import Submission.Work.Implosion.Approx.hasDerivAt_log_sinh_div
import Submission.Work.Implosion.Ecalle.ecallePt_eq_coth

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.PARIMPL2

open Complex
open Work.Implosion

noncomputable section

/-! ## Elementary `cosh`/`log` bounds near `0` -/

private lemma cosh_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖Complex.cosh w - 1‖ ≤ ‖w‖ ^ 2 := by
  have h1 : ‖Complex.exp w - 1 - w‖ ≤ ‖w‖ ^ 2 := Complex.norm_exp_sub_one_sub_id_le hw
  have h2 : ‖Complex.exp (-w) - 1 - (-w)‖ ≤ ‖w‖ ^ 2 := by
    have h := Complex.norm_exp_sub_one_sub_id_le (x := -w) (by rwa [norm_neg])
    rwa [norm_neg] at h
  have hdecomp : Complex.cosh w - 1
      = ((Complex.exp w - 1 - w) + (Complex.exp (-w) - 1 - (-w))) / 2 := by
    rw [Complex.cosh]; ring
  rw [hdecomp, norm_div, Complex.norm_ofNat]
  have hsum : ‖(Complex.exp w - 1 - w) + (Complex.exp (-w) - 1 - (-w))‖ ≤ 2 * ‖w‖ ^ 2 := by
    calc ‖(Complex.exp w - 1 - w) + (Complex.exp (-w) - 1 - (-w))‖
        ≤ ‖Complex.exp w - 1 - w‖ + ‖Complex.exp (-w) - 1 - (-w)‖ := norm_add_le _ _
      _ ≤ ‖w‖ ^ 2 + ‖w‖ ^ 2 := add_le_add h1 h2
      _ = 2 * ‖w‖ ^ 2 := by ring
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith

private lemma re_cosh_pos {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) : 0 < (Complex.cosh w).re := by
  have h1 : ‖Complex.cosh w - 1‖ ≤ ‖w‖ ^ 2 := cosh_sub_one_le (by linarith)
  have h2 : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w, hw]
  have h3 := Complex.abs_re_le_norm (Complex.cosh w - 1)
  have h4 : (Complex.cosh w).re = 1 + (Complex.cosh w - 1).re := by
    rw [Complex.sub_re, Complex.one_re]; ring
  rw [h4]
  have h5 : -‖Complex.cosh w - 1‖ ≤ (Complex.cosh w - 1).re := by
    have := (abs_le.mp h3).1; linarith
  linarith

private lemma norm_log_cosh_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖Complex.log (Complex.cosh w)‖ ≤ 3 / 2 * ‖w‖ ^ 2 := by
  have h1 : ‖Complex.cosh w - 1‖ ≤ ‖w‖ ^ 2 := cosh_sub_one_le (by linarith)
  have h2 : ‖w‖ ^ 2 ≤ 1 / 2 := by nlinarith [norm_nonneg w, hw]
  have hz : ‖Complex.cosh w - 1‖ ≤ 1 / 2 := le_trans h1 h2
  have h3 := Complex.norm_log_one_add_half_le_self hz
  have heq : Complex.log (Complex.cosh w) = Complex.log (1 + (Complex.cosh w - 1)) := by
    congr 1; ring
  rw [heq]
  calc ‖Complex.log (1 + (Complex.cosh w - 1))‖ ≤ 3 / 2 * ‖Complex.cosh w - 1‖ := h3
    _ ≤ 3 / 2 * ‖w‖ ^ 2 := by linarith

/-! ## The Écalle coordinate is `1/ζ` to third order

The proof is that of `Work.Implosion.Approx.ecalCoord_sub_inv_le` (`‖ζ‖ ≥ 1`), stopping one
step earlier: the cubic remainder is retained, and the hypothesis `‖ζ‖ ≥ 1` is only used to
know `ζ ≠ 0`. -/

/-- `logTaylor 3 z = z - z²/2`, the Taylor polynomial of `log (1+z)` up to degree `2`. -/
private lemma ecal_logTaylor_three :
    Complex.logTaylor 3 = fun z : ℂ => z - z ^ 2 / 2 := by
  funext z
  simp only [Complex.logTaylor_succ, Complex.logTaylor_zero, Pi.add_apply]
  ring

/-- Splitting the branch of the logarithm: for `‖w‖ < 1` the number `(1+w)/(1-w)` has
argument in `(-π, π)`, so its logarithm is the sum of the logarithms of `1+w` and `(1-w)⁻¹`. -/
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

/-- **The Écalle coordinate is `1/ζ` to third order** (no lower bound on `‖ζ‖`): for
`a ≠ 0`, `ζ ≠ 0`, `4‖a‖ ≤ ‖ζ‖` one has `‖u(ζ) − 1/ζ‖ ≤ (4/9)‖a‖²/‖ζ‖³`. -/
theorem ecalCoord_sub_inv_le_small (a ζ : ℂ) (ha : a ≠ 0) (hζne : ζ ≠ 0)
    (haζ : 4 * ‖a‖ ≤ ‖ζ‖) :
    ‖ecalCoord a ζ - 1 / ζ‖ ≤ 4 / 9 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hζpos : 0 < ‖ζ‖ := by linarith
  have hζne' : ζ ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hζpos)
  set w : ℂ := a / ζ with hw
  have hwnorm : ‖w‖ = ‖a‖ / ‖ζ‖ := by rw [hw, norm_div]
  have hwq : ‖w‖ ≤ 1 / 4 := by
    rw [hwnorm, div_le_iff₀ hζpos]
    linarith
  -- the Möbius coordinate is `(1+w)/(1-w)` with `w = a/ζ`
  have hmob : mobius a ζ = (1 + w) / (1 - w) := by
    have h1 : 1 + w = (ζ + a) / ζ := by rw [hw, add_div, div_self hζne']
    have h2 : 1 - w = (ζ - a) / ζ := by rw [hw, sub_div, div_self hζne']
    rw [mobius, h1, h2, ← div_div_div_cancel_right₀ hζne' (ζ + a) (ζ - a)]
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

theorem ecalCoord_norm_le_small (a ζ : ℂ) (ha : a ≠ 0) (hζne : ζ ≠ 0)
    (haζ : 4 * ‖a‖ ≤ ‖ζ‖) : ‖ecalCoord a ζ‖ ≤ 2 / ‖ζ‖ := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hζpos : 0 < ‖ζ‖ := by linarith
  have hζne' : ‖ζ‖ ≠ 0 := ne_of_gt hζpos
  have hu_sub := ecalCoord_sub_inv_le_small a ζ ha hζne haζ
  have h1 : ‖ecalCoord a ζ‖ ≤ ‖ecalCoord a ζ - 1/ζ‖ + ‖(1:ℂ)/ζ‖ := by
    calc ‖ecalCoord a ζ‖ = ‖(ecalCoord a ζ - 1/ζ) + 1/ζ‖ := by ring_nf
      _ ≤ ‖ecalCoord a ζ - 1/ζ‖ + ‖(1:ℂ)/ζ‖ := norm_add_le _ _
  have h2 : ‖(1:ℂ)/ζ‖ = 1/‖ζ‖ := by rw [norm_div, norm_one]
  rw [h2] at h1
  have hb2 : 4/9 * ‖a‖^2 ≤ ‖ζ‖^2 := by
    have hb : ‖a‖ ≤ ‖ζ‖/4 := by linarith
    have hb' : ‖a‖^2 ≤ (‖ζ‖/4)^2 := pow_le_pow_left₀ (norm_nonneg a) hb 2
    have hsq : (‖ζ‖/4)^2 = ‖ζ‖^2/16 := by ring
    rw [hsq] at hb'
    nlinarith
  have h3 : 4/9 * ‖a‖^2/‖ζ‖^3 ≤ 1/‖ζ‖ := by
    rw [div_le_iff₀ (pow_pos hζpos 3)]
    have hc : (1/‖ζ‖) * ‖ζ‖^3 = ‖ζ‖^2 := by
      field_simp
    rw [hc]; exact hb2
  calc ‖ecalCoord a ζ‖ ≤ 1/‖ζ‖ + 1/‖ζ‖ := by linarith
    _ = 2/‖ζ‖ := by ring

theorem a_mul_ecalCoord_le_half (a ζ : ℂ) (ha : a ≠ 0) (hζne : ζ ≠ 0)
    (haζ : 4 * ‖a‖ ≤ ‖ζ‖) : ‖a * ecalCoord a ζ‖ ≤ 1/2 := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hζpos : 0 < ‖ζ‖ := by linarith
  have hu_le := ecalCoord_norm_le_small a ζ ha hζne haζ
  have h1 : ‖a * ecalCoord a ζ‖ ≤ 2 * ‖a‖/‖ζ‖ := by
    rw [norm_mul]
    calc ‖a‖ * ‖ecalCoord a ζ‖ ≤ ‖a‖ * (2/‖ζ‖) :=
          mul_le_mul_of_nonneg_left hu_le (norm_nonneg _)
      _ = 2 * ‖a‖/‖ζ‖ := by ring
  have h2 : ‖a‖/‖ζ‖ ≤ 1/4 := by rw [div_le_iff₀ hζpos]; linarith
  have h3 : 2 * ‖a‖/‖ζ‖ ≤ 1/2 := by
    rw [show 2 * ‖a‖/‖ζ‖ = 2 * (‖a‖/‖ζ‖) by ring]
    linarith
  linarith

/-! ## The sign of `Im ζ` on the incoming end -/

theorem im_pos_of_sinh_im_neg_small (lam : ℝ) (ζ : ℂ) (hlam : 0 < lam) (hre : ζ.re < 0)
    (hζle : ‖ζ‖ ≤ 4) (hlamζ : 4 * lam ≤ ‖ζ‖)
    (hwim : (Complex.sinh (((lam : ℂ) * I) * ecalCoord ((lam : ℂ) * I) ζ)
      / ((lam : ℂ) * I)).im < 0) :
    0 < ζ.im := by
  have ha : ((lam : ℂ) * I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hlam)) Complex.I_ne_zero
  have hnorma : ‖((lam : ℂ) * I)‖ = lam := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
    exact abs_of_pos hlam
  have hζpos : 0 < ‖ζ‖ := by
    have := norm_pos_iff.mpr ha
    rw [hnorma] at this
    linarith
  have hζne : ζ ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hζpos)
  have hlt : ‖((lam : ℂ) * I)‖ < ‖ζ‖ := by rw [hnorma]; linarith
  have hza : ζ ≠ (lam : ℂ) * I := by
    intro h; rw [h] at hlt; exact absurd hlt (lt_irrefl ‖(lam : ℂ) * I‖)
  have hzna : ζ ≠ -((lam : ℂ) * I) := by
    intro h; rw [h, norm_neg] at hlt; exact absurd hlt (lt_irrefl ‖(lam : ℂ) * I‖)
  have hpt : ecalPt ((lam : ℂ) * I) (ecalCoord ((lam : ℂ) * I) ζ) = ζ :=
    ecalPt_ecalCoord _ ζ ha hza hzna
  have hhalf : ‖((lam : ℂ) * I) * ecalCoord ((lam : ℂ) * I) ζ‖ ≤ 1/2 := by
    refine a_mul_ecalCoord_le_half _ ζ ha hζne ?_
    rw [hnorma]; exact hlamζ
  have hcosh : 0 < (Complex.cosh (((lam : ℂ) * I) * ecalCoord ((lam : ℂ) * I) ζ)).re :=
    re_cosh_pos hhalf
  have h1 : 0 < (ecalPt ((lam : ℂ) * I) (ecalCoord ((lam : ℂ) * I) ζ)).im :=
    Approx.ecalPt_im_pos_of_sinh_im_neg lam _ hlam hwim hcosh
  rwa [hpt] at h1

/-! ## The main estimate -/

private theorem approxEcal_end_in_small_aux (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a κ ζ : ℂ), a ≠ 0 → ‖κ‖ ≤ K → ζ.re < 0 → 0 < ζ.im →
      ‖ζ‖ ≤ 4 → 4 * ‖a‖ ≤ ‖ζ‖ →
      (Complex.sinh (a * ecalCoord a ζ) / a).im < 0 →
      ‖approxEcal a κ (ecalCoord a ζ + Real.pi * I / a)
        - (Real.pi * I / a + Real.pi * I * κ + ((1 / ζ) - κ * Complex.log ζ))‖
      ≤ C * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 := by
  refine ⟨4 / 9 + 24 * K, by linarith, ?_⟩
  intro a κ ζ ha hκ hre him hζle haζ hwim
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hζpos : 0 < ‖ζ‖ := by linarith
  have hζne : ζ ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hζpos)
  have hlt : ‖a‖ < ‖ζ‖ := by linarith
  have hza : ζ ≠ a := by intro h; rw [h] at hlt; exact absurd hlt (lt_irrefl ‖a‖)
  have hzna : ζ ≠ -a := by intro h; rw [h, norm_neg] at hlt; exact absurd hlt (lt_irrefl ‖a‖)
  set u : ℂ := ecalCoord a ζ with hudef
  have hwimu : (Complex.sinh (a * u) / a).im < 0 := by rw [hudef]; exact hwim
  have hu_sub : ‖u - 1/ζ‖ ≤ 4/9 * ‖a‖^2/‖ζ‖^3 := by
    rw [hudef]; exact ecalCoord_sub_inv_le_small a ζ ha hζne haζ
  have hu_le : ‖u‖ ≤ 2/‖ζ‖ := by
    have h1 : ‖u‖ ≤ ‖u - 1/ζ‖ + ‖(1:ℂ)/ζ‖ := by
      calc ‖u‖ = ‖(u - 1/ζ) + 1/ζ‖ := by ring_nf
        _ ≤ ‖u - 1/ζ‖ + ‖(1:ℂ)/ζ‖ := norm_add_le _ _
    have h2 : ‖(1:ℂ)/ζ‖ = 1/‖ζ‖ := by rw [norm_div, norm_one]
    rw [h2] at h1
    have hb2 : 4/9 * ‖a‖^2 ≤ ‖ζ‖^2 := by
      have hb : ‖a‖ ≤ ‖ζ‖/4 := by linarith
      have hb' : ‖a‖^2 ≤ (‖ζ‖/4)^2 := pow_le_pow_left₀ (norm_nonneg a) hb 2
      have hsq : (‖ζ‖/4)^2 = ‖ζ‖^2/16 := by ring
      rw [hsq] at hb'
      nlinarith
    have h3 : 4/9 * ‖a‖^2/‖ζ‖^3 ≤ 1/‖ζ‖ := by
      rw [div_le_iff₀ (pow_pos hζpos 3)]
      have hc : (1/‖ζ‖) * ‖ζ‖^3 = ‖ζ‖^2 := by
        field_simp
      rw [hc]; exact hb2
    calc ‖u‖ ≤ 1/‖ζ‖ + 1/‖ζ‖ := by linarith
      _ = 2/‖ζ‖ := by ring
  have hau_le : ‖a * u‖ ≤ 2 * ‖a‖/‖ζ‖ := by
    rw [norm_mul]
    calc ‖a‖ * ‖u‖ ≤ ‖a‖ * (2/‖ζ‖) := mul_le_mul_of_nonneg_left hu_le (norm_nonneg _)
      _ = 2 * ‖a‖/‖ζ‖ := by ring
  have hau : ‖a * u‖ ≤ 1/2 := by
    have h2 : ‖a‖/‖ζ‖ ≤ 1/4 := by rw [div_le_iff₀ hζpos]; linarith
    have h3 : 2 * ‖a‖/‖ζ‖ ≤ 1/2 := by
      rw [show 2 * ‖a‖/‖ζ‖ = 2 * (‖a‖/‖ζ‖) by ring]
      linarith
    linarith
  have hau2 : ‖a * u‖^2 ≤ 4 * ‖a‖^2/‖ζ‖^2 := by
    calc ‖a * u‖^2 ≤ (2 * ‖a‖/‖ζ‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hau_le 2
      _ = 4 * ‖a‖^2/‖ζ‖^2 := by ring
  have hw0 : Complex.sinh (a * u)/a ≠ 0 := by
    intro hcon
    have hz : (Complex.sinh (a * u)/a).im = 0 := by rw [hcon]; simp
    linarith
  have hsinh_ne : Complex.sinh (a * u) ≠ 0 := by
    intro hcon; exact hw0 (by rw [hcon, zero_div])
  have hEne : ecalE a u ≠ 1 := by
    intro hcon
    refine hsinh_ne (Approx.sinh_eq_zero_of_exp_two_mul_eq_one (a * u) ?_)
    rw [ecalE] at hcon
    rw [show (2 : ℂ) * (a * u) = 2 * a * u by ring]
    exact hcon
  have hpt : ecalPt a u = ζ := by
    rw [hudef]; exact ecalPt_ecalCoord a ζ ha hza hzna
  have hcoth : ecalPt a u = a * coth (a * u) := Ecalle.ecallePt_eq_coth a u hEne
  have hζeq : ζ = a * (Complex.cosh (a * u)/Complex.sinh (a * u)) := by
    rw [← hpt, hcoth, coth]
  have hmul : ζ * Complex.sinh (a * u) = a * Complex.cosh (a * u) := by
    rw [hζeq]; field_simp; try ring
  have hwζ : (Complex.sinh (a * u)/a) * ζ = Complex.cosh (a * u) := by
    rw [div_mul_eq_mul_div, mul_comm (Complex.sinh (a * u)) ζ, hmul, mul_div_cancel_left₀ _ ha]
  have hwarg_lt : (Complex.sinh (a * u)/a).arg < 0 := Complex.arg_neg_iff.mpr hwimu
  have hζarg_gt : Real.pi/2 < ζ.arg := by
    by_contra hcon
    rw [not_lt] at hcon
    rcases (Complex.arg_le_pi_div_two_iff.mp hcon) with h' | h'
    · linarith
    · linarith
  have hargcond : (Complex.sinh (a * u)/a).arg + ζ.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [Set.mem_Ioc]
    refine ⟨?_, ?_⟩
    · have h1 := Complex.neg_pi_lt_arg (Complex.sinh (a * u)/a)
      linarith [Real.pi_pos]
    · have h1 := hwarg_lt
      have h2 := Complex.arg_le_pi ζ
      linarith
  have hlogmul := Complex.log_mul hw0 hζne hargcond
  have hlogrel : Complex.log (Complex.sinh (a * u)/a) + Complex.log ζ
      = Complex.log (Complex.cosh (a * u)) := by
    rw [← hlogmul, hwζ]
  have hlog : ‖Complex.log (Complex.sinh (a * u)/a) + Complex.log ζ‖
      ≤ 6 * ‖a‖^2/‖ζ‖^2 := by
    rw [hlogrel]
    have hL : ‖Complex.log (Complex.cosh (a * u))‖ ≤ 3/2 * ‖a * u‖^2 :=
      norm_log_cosh_le hau
    have h2 : (3/2:ℝ) * ‖a * u‖^2 ≤ 6 * ‖a‖^2/‖ζ‖^2 := by
      calc (3/2:ℝ) * ‖a * u‖^2 ≤ (3/2) * (4 * ‖a‖^2/‖ζ‖^2) :=
            mul_le_mul_of_nonneg_left hau2 (by norm_num)
        _ = 6 * ‖a‖^2/‖ζ‖^2 := by ring
    linarith
  have hshift := Approx.approxEcal_shift a κ u ha hwimu
  have hmain : approxEcal a κ (u + Real.pi * I / a)
      - (Real.pi * I / a + Real.pi * I * κ + (1/ζ - κ * Complex.log ζ))
      = (u - 1/ζ) + κ * (Complex.log (Complex.sinh (a * u)/a) + Complex.log ζ) := by
    rw [hshift, approxEcal_apply]
    ring
  rw [hmain]
  have h1 : ‖(u - 1/ζ) + κ * (Complex.log (Complex.sinh (a * u)/a) + Complex.log ζ)‖
      ≤ ‖u - 1/ζ‖ + ‖κ‖ * ‖Complex.log (Complex.sinh (a * u)/a) + Complex.log ζ‖ := by
    calc ‖(u - 1/ζ) + κ * (Complex.log (Complex.sinh (a * u)/a) + Complex.log ζ)‖
        ≤ ‖u - 1/ζ‖ + ‖κ * (Complex.log (Complex.sinh (a * u)/a) + Complex.log ζ)‖ :=
          norm_add_le _ _
      _ = ‖u - 1/ζ‖ + ‖κ‖ * ‖Complex.log (Complex.sinh (a * u)/a) + Complex.log ζ‖ := by
          rw [norm_mul]
  have h2 : ‖κ‖ * ‖Complex.log (Complex.sinh (a * u)/a) + Complex.log ζ‖
      ≤ K * (6 * ‖a‖^2/‖ζ‖^2) := mul_le_mul hκ hlog (norm_nonneg _) hK
  have h6 : 6 * ‖a‖^2/‖ζ‖^2 ≤ 24 * ‖a‖^2/‖ζ‖^3 := by
    have hζp3 : 0 < ‖ζ‖^3 := pow_pos hζpos 3
    have hcoef : 0 ≤ 6 * ‖a‖^2/‖ζ‖^3 :=
      div_nonneg (mul_nonneg (by norm_num) (sq_nonneg ‖a‖)) (le_of_lt hζp3)
    have h1 : 6 * ‖a‖^2/‖ζ‖^2 = (6 * ‖a‖^2/‖ζ‖^3) * ‖ζ‖ := by field_simp
    have h2 : (6 * ‖a‖^2/‖ζ‖^3) * ‖ζ‖ ≤ (6 * ‖a‖^2/‖ζ‖^3) * 4 :=
      mul_le_mul_of_nonneg_left hζle hcoef
    have h3 : (6 * ‖a‖^2/‖ζ‖^3) * 4 = 24 * ‖a‖^2/‖ζ‖^3 := by ring
    linarith
  have h3 : K * (6 * ‖a‖^2/‖ζ‖^2) ≤ 24 * K * ‖a‖^2/‖ζ‖^3 := by
    rw [show 24 * K * ‖a‖^2/‖ζ‖^3 = K * (24 * ‖a‖^2/‖ζ‖^3) by ring]
    exact mul_le_mul_of_nonneg_left h6 hK
  calc ‖(u - 1/ζ) + κ * (Complex.log (Complex.sinh (a * u)/a) + Complex.log ζ)‖
      ≤ ‖u - 1/ζ‖ + ‖κ‖ * ‖Complex.log (Complex.sinh (a * u)/a) + Complex.log ζ‖ := h1
    _ ≤ 4/9 * ‖a‖^2/‖ζ‖^3 + K * (6 * ‖a‖^2/‖ζ‖^2) := add_le_add hu_sub h2
    _ ≤ 4/9 * ‖a‖^2/‖ζ‖^3 + 24 * K * ‖a‖^2/‖ζ‖^3 := add_le_add le_rfl h3
    _ = (4/9 + 24 * K) * ‖a‖^2/‖ζ‖^3 := by ring

/-! ## The instantiation -/

theorem approxEcal_end_in_small (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : ℝ) (κ ζ : ℂ), 0 < lam → ‖κ‖ ≤ K → ζ.re < 0 →
      ‖ζ‖ ≤ 4 → 4 * lam ≤ ‖ζ‖ →
      (Complex.sinh (((lam : ℂ) * I) * Work.Implosion.ecalCoord ((lam : ℂ) * I) ζ)
        / ((lam : ℂ) * I)).im < 0 →
      ‖Work.Implosion.approxEcal ((lam : ℂ) * I) κ
          (Work.Implosion.ecalCoord ((lam : ℂ) * I) ζ + Real.pi * I / ((lam : ℂ) * I))
        - (Real.pi * I / ((lam : ℂ) * I) + Real.pi * I * κ + ((1 / ζ) - κ * Complex.log ζ))‖
      ≤ C * lam ^ 2 / ‖ζ‖ ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := approxEcal_end_in_small_aux K hK
  refine ⟨C, hC0, ?_⟩
  intro lam κ ζ hlam hκ hre hζle hlamζ hwim
  have ha : ((lam : ℂ) * I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hlam)) Complex.I_ne_zero
  have hnorma : ‖((lam : ℂ) * I)‖ = lam := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
    exact abs_of_pos hlam
  have him : 0 < ζ.im := im_pos_of_sinh_im_neg_small lam ζ hlam hre hζle hlamζ hwim
  have h4 : 4 * ‖((lam : ℂ) * I)‖ ≤ ‖ζ‖ := by rw [hnorma]; exact hlamζ
  have h := hC ((lam : ℂ) * I) κ ζ ha hκ hre him hζle h4 hwim
  rwa [hnorma] at h


end

end Work.PARIMPL2
