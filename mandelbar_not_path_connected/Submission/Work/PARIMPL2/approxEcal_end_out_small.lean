/-
Copyright: subproject `Submission/Work/PARIMPL2/` of `mandelbar_not_path_connected`.

# `Work.PARIMPL2.approxEcal_end_out_small` — the outgoing end at *small* `‖ζ‖`

The delivered Implosion asymptotics for the outgoing end,
`Work.Implosion.Approx.approxEcal_end_out`, is stated in the regime `‖ζ‖ ≥ 1`, `‖a‖ ≤ 1`, and
with the (coarser) error `O(‖a‖²/‖ζ‖²)`.  The MATCH comparison of `Work.PARIMPL2.MatchCore`
lives on a window at `‖chartZeta‖ ≈ 1/R < 1`, so the asymptotics is needed in the *small*-`‖ζ‖`
form (`Submission/Work/PARIMPL2/NOTES.md` §6): the regime is `ζ.re > 0`, `‖ζ‖ ≤ 4`,
`4‖a‖ ≤ ‖ζ‖`, and the error is the *sharp* one `O(‖a‖²/‖ζ‖³)`.

The statement is homogeneous in the scaling `ζ ↦ tζ`, `a ↦ ta` (the error `‖a‖²/‖ζ‖³` has
degree `-1`, like the leading correction `1/ζ`), so it is *not* a consequence of the `‖ζ‖ ≥ 1`
statement; but the very same proof goes through with the sharp exponent.  The hypothesis
`‖ζ‖ ≤ 4` is what converts the sub-leading `O(‖a‖²/‖ζ‖²)` contribution of `log (cosh (a·u))`
into `O(‖a‖²/‖ζ‖³)`.

Adapted from `Work.Implosion.Approx.approxEcal_end_out` with two changes:

* the Écalle-coordinate expansion retains its cubic remainder
  (`ecalCoord_sub_inv_le_small` below), so no lower bound on `‖ζ‖` is needed;
* hence the constant is `4/9 + 24K` for the sharp exponent, and the hypothesis `‖a‖ ≤ 1`
  disappears (the smallness `‖a·u‖ ≤ 1/2` follows from `4‖a‖ ≤ ‖ζ‖` alone).

Everything else is verbatim: `ecalPt_ecalCoord`, the cotangent identity
`Ecalle.ecallePt_eq_coth`, the logarithmic identity
`log (sinh (a·u)/a) + log ζ = log (cosh (a·u))` with its branch bookkeeping, and the
elementary bounds `‖cosh w − 1‖ ≤ ‖w‖²`, `Re (cosh w) > 0`, `‖log (cosh w)‖ ≤ (3/2)‖w‖²`
for `‖w‖ ≤ 1/2`.
-/
import Mathlib
import Submission.Work.Implosion.Approx
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

/-! ## The Écalle coordinate is `1/ζ` to third order, with no lower bound on `‖ζ‖` -/

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

/-! ## The main estimate -/

theorem approxEcal_end_out_small (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a κ ζ : ℂ), a ≠ 0 → ‖κ‖ ≤ K → 0 < ζ.re → ‖ζ‖ ≤ 4 →
      4 * ‖a‖ ≤ ‖ζ‖ →
      Complex.sinh (a * Work.Implosion.ecalCoord a ζ) / a ∈ Complex.slitPlane →
      ‖Work.Implosion.approxEcal a κ (Work.Implosion.ecalCoord a ζ)
        - ((1 / ζ) - κ * Complex.log ζ)‖ ≤ C * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 := by
  refine ⟨4 / 9 + 24 * K, by linarith, ?_⟩
  intro a κ ζ ha hκ hre hζle haζ hslit
  have hζpos : 0 < ‖ζ‖ := lt_of_lt_of_le hre (Complex.re_le_norm ζ)
  have hζne : ζ ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hζpos)
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set u : ℂ := ecalCoord a ζ with hu
  have hslit' : Complex.sinh (a * u) / a ∈ Complex.slitPlane := by rw [hu]; exact hslit
  -- (β) the Écalle coordinate is `1/ζ` to third order
  have hu_sub : ‖u - 1 / ζ‖ ≤ 4 / 9 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 := by
    rw [hu]; exact ecalCoord_sub_inv_le_small a ζ ha hζne haζ
  have hfour : ‖a‖ ≤ ‖ζ‖ / 4 := by linarith
  have hlt : ‖a‖ < ‖ζ‖ := by linarith
  have h1a : ζ ≠ a := by intro h; rw [h] at hlt; exact absurd hlt (lt_irrefl ‖a‖)
  have h2a : ζ ≠ -a := by intro h; rw [h, norm_neg] at hlt; exact absurd hlt (lt_irrefl ‖a‖)
  -- (γ) hence `u` is small, of size `2/‖ζ‖`
  have hu_le : ‖u‖ ≤ 2 / ‖ζ‖ := by
    have h1 : ‖u‖ ≤ ‖u - 1 / ζ‖ + ‖(1 : ℂ) / ζ‖ := by
      calc ‖u‖ = ‖(u - 1 / ζ) + 1 / ζ‖ := by ring_nf
        _ ≤ ‖u - 1 / ζ‖ + ‖(1 : ℂ) / ζ‖ := norm_add_le _ _
    have h2 : ‖(1 : ℂ) / ζ‖ = 1 / ‖ζ‖ := by rw [norm_div, norm_one]
    rw [h2] at h1
    have hb2 : 4 / 9 * ‖a‖ ^ 2 ≤ ‖ζ‖ ^ 2 := by
      have hb' : ‖a‖ ^ 2 ≤ (‖ζ‖ / 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg a) hfour 2
      have hsq : (‖ζ‖ / 4) ^ 2 = ‖ζ‖ ^ 2 / 16 := by ring
      rw [hsq] at hb'
      nlinarith
    have h3 : 4 / 9 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 ≤ 1 / ‖ζ‖ := by
      rw [div_le_iff₀ (pow_pos hζpos 3)]
      have hc : (1 / ‖ζ‖) * ‖ζ‖ ^ 3 = ‖ζ‖ ^ 2 := by field_simp
      rw [hc]; exact hb2
    have hfin : ‖u‖ ≤ 1 / ‖ζ‖ + 1 / ‖ζ‖ := by linarith
    calc ‖u‖ ≤ 1 / ‖ζ‖ + 1 / ‖ζ‖ := hfin
      _ = 2 / ‖ζ‖ := by ring
  have hau_le : ‖a * u‖ ≤ 2 * ‖a‖ / ‖ζ‖ := by
    rw [norm_mul]
    calc ‖a‖ * ‖u‖ ≤ ‖a‖ * (2 / ‖ζ‖) := mul_le_mul_of_nonneg_left hu_le (norm_nonneg _)
      _ = 2 * ‖a‖ / ‖ζ‖ := by ring
  have hau : ‖a * u‖ ≤ 1 / 2 := by
    have h2 : ‖a‖ / ‖ζ‖ ≤ 1 / 4 := by rw [div_le_iff₀ hζpos]; linarith
    have h3 : 2 * ‖a‖ / ‖ζ‖ ≤ 1 / 2 := by
      rw [show 2 * ‖a‖ / ‖ζ‖ = 2 * (‖a‖ / ‖ζ‖) by ring]; linarith
    linarith
  have hau2 : ‖a * u‖ ^ 2 ≤ 4 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by
    calc ‖a * u‖ ^ 2 ≤ (2 * ‖a‖ / ‖ζ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hau_le 2
      _ = 4 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by ring
  -- no punctures: `sinh (a·u) ≠ 0`
  have hsinh_ne : Complex.sinh (a * u) ≠ 0 := by
    intro h
    exact Complex.slitPlane_ne_zero hslit' (by rw [h, zero_div])
  have hEne : ecalE a u ≠ 1 := by
    intro h
    refine hsinh_ne (Approx.sinh_eq_zero_of_exp_two_mul_eq_one (a * u) ?_)
    rw [ecalE] at h
    rw [show (2 : ℂ) * (a * u) = 2 * a * u by ring]
    exact h
  -- the exact identity `sinh (a·u)/a = cosh (a·u)/ζ`
  have hpt : ecalPt a u = ζ := by
    rw [hu]; exact ecalPt_ecalCoord a ζ ha h1a h2a
  have hcoth : ecalPt a u = a * coth (a * u) := Ecalle.ecallePt_eq_coth a u hEne
  have hζeq : ζ = a * (Complex.cosh (a * u) / Complex.sinh (a * u)) := by
    rw [← hpt, hcoth, coth]
  have hmul : ζ * Complex.sinh (a * u) = a * Complex.cosh (a * u) := by
    rw [hζeq]; field_simp; try ring
  have hid : Complex.sinh (a * u) / a = Complex.cosh (a * u) * ζ⁻¹ := by
    rw [← div_eq_mul_inv]
    rw [div_eq_div_iff ha hζne]
    rw [mul_comm (Complex.sinh (a * u)) ζ, mul_comm (Complex.cosh (a * u)) a]
    exact hmul
  -- the logarithmic identity `log (sinh(a·u)/a) + log ζ = log (cosh (a·u))`
  have hcosh_re : 0 < (Complex.cosh (a * u)).re := re_cosh_pos hau
  have hzeta_inv_re : 0 < (ζ⁻¹).re := by
    rw [Complex.inv_re, Complex.normSq_eq_norm_sq]
    have hnorm : (0:ℝ) < ‖ζ‖ ^ 2 := by positivity
    exact div_pos hre hnorm
  have harg1 : |(Complex.cosh (a * u)).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hcosh_re)
  have harg2 : |(ζ⁻¹).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hzeta_inv_re)
  have hcosh_ne : Complex.cosh (a * u) ≠ 0 := by
    intro h; rw [h] at hcosh_re; simp at hcosh_re
  have hsum : (Complex.cosh (a * u)).arg + (ζ⁻¹).arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [Set.mem_Ioc]
    have h1 := abs_lt.mp harg1
    have h2 := abs_lt.mp harg2
    constructor <;> linarith [Real.pi_pos]
  have hlogmul : Complex.log (Complex.cosh (a * u) * ζ⁻¹)
      = Complex.log (Complex.cosh (a * u)) + Complex.log (ζ⁻¹) :=
    Complex.log_mul hcosh_ne (inv_ne_zero hζne) hsum
  have hargζ_ne : ζ.arg ≠ Real.pi := by
    have hargζ_lt : |ζ.arg| < Real.pi / 2 :=
      Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
    intro h
    rw [h, abs_of_pos Real.pi_pos] at hargζ_lt
    linarith [Real.pi_pos]
  have hloginv : Complex.log (ζ⁻¹) = -Complex.log ζ := Complex.log_inv ζ hargζ_ne
  have hlogrel : Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ
      = Complex.log (Complex.cosh (a * u)) := by
    have hstep : Complex.log (Complex.sinh (a * u) / a)
        = Complex.log (Complex.cosh (a * u)) + Complex.log (ζ⁻¹) := by
      rw [hid]; exact hlogmul
    rw [hstep, hloginv]; ring
  have hcosh_log : ‖Complex.log (Complex.cosh (a * u))‖ ≤ 3 / 2 * ‖a * u‖ ^ 2 :=
    norm_log_cosh_le hau
  -- the `log (cosh)` contribution is `O(‖a‖²/‖ζ‖²)`, hence `O(‖a‖²/‖ζ‖³)` since `‖ζ‖ ≤ 4`
  have hlog_le : ‖Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ‖
      ≤ 6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by
    rw [hlogrel]
    calc ‖Complex.log (Complex.cosh (a * u))‖ ≤ 3 / 2 * ‖a * u‖ ^ 2 := hcosh_log
      _ ≤ 3 / 2 * (4 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2) := mul_le_mul_of_nonneg_left hau2 (by norm_num)
      _ = 6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by ring
  have h6 : 6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 ≤ 24 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 := by
    have hcoef : 0 ≤ 6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 :=
      div_nonneg (by positivity) (le_of_lt (pow_pos hζpos 3))
    have heq : 6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 = (6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3) * ‖ζ‖ := by field_simp
    calc 6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 = (6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3) * ‖ζ‖ := heq
      _ ≤ (6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3) * 4 := mul_le_mul_of_nonneg_left hζle hcoef
      _ = 24 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 := by ring
  -- assembly
  have hmain : approxEcal a κ u - (1 / ζ - κ * Complex.log ζ)
      = (u - 1 / ζ) + κ * (Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ) := by
    rw [approxEcal_apply]; ring
  rw [hmain]
  have hstep1 : ‖(u - 1 / ζ) + κ * (Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ)‖
      ≤ ‖u - 1 / ζ‖ + ‖κ‖ * ‖Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ‖ := by
    calc ‖(u - 1 / ζ) + κ * (Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ)‖
        ≤ ‖u - 1 / ζ‖ + ‖κ * (Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ)‖ :=
          norm_add_le _ _
      _ = ‖u - 1 / ζ‖ + ‖κ‖ * ‖Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ‖ := by
          rw [norm_mul]
  have hstep2 : ‖κ‖ * ‖Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ‖
      ≤ K * (6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2) := mul_le_mul hκ hlog_le (norm_nonneg _) hK
  have hstep3 : K * (6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2) ≤ 24 * K * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 := by
    rw [show 24 * K * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 = K * (24 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3) by ring]
    exact mul_le_mul_of_nonneg_left h6 hK
  calc ‖(u - 1 / ζ) + κ * (Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ)‖
      ≤ ‖u - 1 / ζ‖ + ‖κ‖ * ‖Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ‖ :=
        hstep1
    _ ≤ 4 / 9 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 + K * (6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2) := add_le_add hu_sub hstep2
    _ ≤ 4 / 9 * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 + 24 * K * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 := add_le_add le_rfl hstep3
    _ = (4 / 9 + 24 * K) * ‖a‖ ^ 2 / ‖ζ‖ ^ 3 := by ring

end

end Work.PARIMPL2
