import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Disp
import Submission.Work.Implosion.Approx
import Submission.Work.Implosion.Ecalle.ecallePt_eq_coth
import Submission.Work.Implosion.Approx.hasDerivAt_log_sinh_div
import Submission.Work.Implosion.Approx.ecalCoord_sub_inv_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Approx

open Complex

/-! ## Elementary `cosh`/`log` bounds near `0`

These are the small-argument facts used to compare
`log (sinh (a·u)/a)` with `log (cosh (a·u))`. -/

/-- `‖cosh w − 1‖ ≤ ‖w‖²` for `‖w‖ ≤ 1`.  This is
`cosh w − 1 = ((e^w − 1 − w) + (e^{−w} − 1 + w))/2` together with Mathlib's
second-order bound `Complex.norm_exp_sub_one_sub_id_le`. -/
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

/-- `Re (cosh w) > 0` for `‖w‖ ≤ 1/2`. -/
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

/-- `‖log (cosh w)‖ ≤ (3/2)·‖w‖²` for `‖w‖ ≤ 1/2`. -/
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

/-! ## The main estimate -/

/-- **The perturbed Fatou coordinate is `1/ζ − κ log ζ` to second order.**

For `‖ζ‖ ≥ 1`, `4‖a‖ ≤ ‖ζ‖`, `‖a‖ ≤ 1`, the approximate perturbed Fatou
coordinate `Ũ(u) = u + κ·log(sinh(a·u)/a)` evaluated at `u = u(ζ) = ecalCoord a ζ`
differs from `1/ζ − κ·log ζ` by `O(‖a‖²/‖ζ‖²)`, uniformly in `ζ` and in `κ` of
norm at most `K`.

The two ingredients are `ecalCoord_sub_inv_le` (the Écalle coordinate is `1/ζ`
to second order) and the identity
`log (sinh(a·u)/a) + log ζ = log (cosh(a·u))`, where `sinh(a·u)/a = cosh(a·u)/ζ`
comes from `ζ = a·coth(a·u)`. -/
theorem approxEcal_end_out (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a κ ζ : ℂ), a ≠ 0 → 0 < ζ.re → 1 ≤ ‖ζ‖ → ‖κ‖ ≤ K →
      Complex.sinh (a * ecalCoord a ζ) / a ∈ Complex.slitPlane →
      4 * ‖a‖ ≤ ‖ζ‖ → ‖a‖ ≤ 1 →
      ‖approxEcal a κ (ecalCoord a ζ) - ((1 / ζ) - κ * Complex.log ζ)‖
        ≤ C * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by
  refine ⟨4 / 9 + 6 * K, by linarith, ?_⟩
  intro a κ ζ ha hre hζ hκ hslit haζ ha1
  have hζpos : 0 < ‖ζ‖ := lt_of_lt_of_le zero_lt_one hζ
  have hζne : ζ ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hζpos)
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set u : ℂ := ecalCoord a ζ with hu
  -- (β) the Écalle coordinate is `1/ζ` to second order
  have hu_sub : ‖u - 1 / ζ‖ ≤ 4 / 9 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by
    rw [hu]; exact ecalCoord_sub_inv_le a ζ ha hζ haζ
  -- (γ) hence `u` is small, of size `1/‖ζ‖`
  have hu_le : ‖u‖ ≤ 2 / ‖ζ‖ := by
    have h1 : ‖u‖ ≤ ‖u - 1 / ζ‖ + ‖(1 : ℂ) / ζ‖ := by
      calc ‖u‖ = ‖(u - 1 / ζ) + 1 / ζ‖ := by ring_nf
        _ ≤ ‖u - 1 / ζ‖ + ‖1 / ζ‖ := norm_add_le _ _
    have hnorm_inv : ‖(1 : ℂ) / ζ‖ = 1 / ‖ζ‖ := by rw [norm_div, norm_one]
    rw [hnorm_inv] at h1
    have hb2 : 4 / 9 * ‖a‖ ^ 2 ≤ ‖ζ‖ := by
      have h9 : ‖a‖ / 9 ≤ 1 := by linarith
      calc 4 / 9 * ‖a‖ ^ 2 = (4 * ‖a‖) * (‖a‖ / 9) := by ring
        _ ≤ ‖ζ‖ * 1 := mul_le_mul haζ h9 (by positivity) (by positivity)
        _ = ‖ζ‖ := by ring
    have hb : 4 / 9 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 ≤ 1 / ‖ζ‖ := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < ‖ζ‖ ^ 2)]
      have hsq : (1 / ‖ζ‖) * ‖ζ‖ ^ 2 = ‖ζ‖ := by
        rw [one_div, inv_mul_eq_iff_eq_mul₀ (ne_of_gt hζpos), sq]
      rw [hsq]; exact hb2
    have hfin : ‖u‖ ≤ 1 / ‖ζ‖ + 1 / ‖ζ‖ := by linarith
    calc ‖u‖ ≤ 1 / ‖ζ‖ + 1 / ‖ζ‖ := hfin
      _ = 2 / ‖ζ‖ := by ring
  have hau_le : ‖a * u‖ ≤ 2 * ‖a‖ / ‖ζ‖ := by
    rw [norm_mul]
    calc ‖a‖ * ‖u‖ ≤ ‖a‖ * (2 / ‖ζ‖) := mul_le_mul_of_nonneg_left hu_le (norm_nonneg _)
      _ = 2 * ‖a‖ / ‖ζ‖ := by ring
  have hau : ‖a * u‖ ≤ 1 / 2 := by
    have h1 : ‖a‖ / ‖ζ‖ ≤ 1 / 4 := by rw [div_le_iff₀ hζpos]; linarith
    have h2 : 2 * ‖a‖ / ‖ζ‖ ≤ 1 / 2 := by rw [mul_div_assoc]; linarith
    linarith
  have hau2 : ‖a * u‖ ^ 2 ≤ 4 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by
    calc ‖a * u‖ ^ 2 ≤ (2 * ‖a‖ / ‖ζ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hau_le 2
      _ = 4 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by ring
  -- the two fixed points are far from `ζ`
  have hlt : ‖a‖ < ‖ζ‖ := by
    by_contra hc
    rw [not_lt] at hc
    linarith
  have h1a : ζ ≠ a := by
    intro h; rw [h] at hlt; exact absurd hlt (lt_irrefl ‖a‖)
  have h2a : ζ ≠ -a := by
    intro h; rw [h, norm_neg] at hlt; exact absurd hlt (lt_irrefl ‖a‖)
  -- no punctures: `sinh (a·u) ≠ 0`
  have hsinh_ne : Complex.sinh (a * u) ≠ 0 := by
    intro h
    exact Complex.slitPlane_ne_zero hslit (by rw [h, zero_div])
  have hEne : ecalE a u ≠ 1 := by
    intro h
    refine hsinh_ne (sinh_eq_zero_of_exp_two_mul_eq_one (a * u) ?_)
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
    have hz0 : ζ ≠ 0 := hζne
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
      ≤ K * (6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2) := by
    have h1 : ‖Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ‖
        ≤ 3 / 2 * ‖a * u‖ ^ 2 := by rw [hlogrel]; exact hcosh_log
    have h2 : (3 / 2 : ℝ) * ‖a * u‖ ^ 2 ≤ 6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by
      calc (3 / 2 : ℝ) * ‖a * u‖ ^ 2 ≤ (3 / 2) * (4 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hau2 (by norm_num)
        _ = 6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by ring
    calc ‖κ‖ * ‖Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ‖
        ≤ K * ‖Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ‖ :=
          mul_le_mul_of_nonneg_right hκ (norm_nonneg _)
      _ ≤ K * (3 / 2 * ‖a * u‖ ^ 2) := mul_le_mul_of_nonneg_left h1 hK
      _ ≤ K * (6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hK
  calc ‖(u - 1 / ζ) + κ * (Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ)‖
      ≤ ‖u - 1 / ζ‖ + ‖κ‖ * ‖Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ‖ := hstep1
    _ ≤ 4 / 9 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 + K * (6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2) := add_le_add hu_sub hstep2
    _ = (4 / 9 + 6 * K) * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by ring

end Work.Implosion.Approx
