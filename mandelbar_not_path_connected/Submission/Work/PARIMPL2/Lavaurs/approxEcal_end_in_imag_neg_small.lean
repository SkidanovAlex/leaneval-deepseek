import Mathlib
import Submission.Work.PARIMPL2.approxEcal_end_in_small
import Submission.Work.Implosion.Approx.approxEcal_end_in_imaginary_neg

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.PARIMPL2.Lavaurs

open Complex
open Work.Implosion

noncomputable section

/-! ## Elementary `cosh`/`log` bounds near `0` -/

private lemma Lcosh_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖Complex.cosh w - 1‖ ≤ ‖w‖ ^ 2 := by
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

private lemma Lre_cosh_pos {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) : 0 < (Complex.cosh w).re := by
  have h1 : ‖Complex.cosh w - 1‖ ≤ ‖w‖ ^ 2 := Lcosh_sub_one_le (by linarith)
  have h2 : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w, hw]
  have h3 := Complex.abs_re_le_norm (Complex.cosh w - 1)
  have h4 : (Complex.cosh w).re = 1 + (Complex.cosh w - 1).re := by
    rw [Complex.sub_re, Complex.one_re]; ring
  rw [h4]
  have h5 : -‖Complex.cosh w - 1‖ ≤ (Complex.cosh w - 1).re := by
    have := (abs_le.mp h3).1; linarith
  linarith

private lemma Lnorm_log_cosh_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖Complex.log (Complex.cosh w)‖ ≤ 3 / 2 * ‖w‖ ^ 2 := by
  have h1 : ‖Complex.cosh w - 1‖ ≤ ‖w‖ ^ 2 := Lcosh_sub_one_le (by linarith)
  have h2 : ‖w‖ ^ 2 ≤ 1 / 2 := by nlinarith [norm_nonneg w, hw]
  have hz : ‖Complex.cosh w - 1‖ ≤ 1 / 2 := le_trans h1 h2
  have h3 := Complex.norm_log_one_add_half_le_self hz
  have heq : Complex.log (Complex.cosh w) = Complex.log (1 + (Complex.cosh w - 1)) := by
    congr 1; ring
  rw [heq]
  calc ‖Complex.log (1 + (Complex.cosh w - 1))‖ ≤ 3 / 2 * ‖Complex.cosh w - 1‖ := h3
    _ ≤ 3 / 2 * ‖w‖ ^ 2 := by linarith

/-! ## The sign of `Im ζ` on the lower incoming end -/

/-- Mirror of `im_pos_of_sinh_im_neg_small`: on the branch `0 < Im (sinh (a·u)/a)` at
`a = iλ`, `u = ecalCoord (iλ) ζ`, the point `ζ` has `Im ζ < 0`. -/
private theorem im_neg_of_sinh_im_pos_small (lam : ℝ) (ζ : ℂ) (hlam : 0 < lam) (hre : ζ.re < 0)
    (hζle : ‖ζ‖ ≤ 4) (hlamζ : 4 * lam ≤ ‖ζ‖)
    (hwim : 0 < (Complex.sinh (((lam : ℂ) * I) * ecalCoord ((lam : ℂ) * I) ζ)
      / ((lam : ℂ) * I)).im) :
    ζ.im < 0 := by
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
  have hhalf : ‖((lam : ℂ) * I) * ecalCoord ((lam : ℂ) * I) ζ‖ ≤ 1 / 2 := by
    refine a_mul_ecalCoord_le_half _ ζ ha hζne ?_
    rw [hnorma]; exact hlamζ
  have hcosh : 0 < (Complex.cosh (((lam : ℂ) * I) * ecalCoord ((lam : ℂ) * I) ζ)).re :=
    Lre_cosh_pos hhalf
  have h1 : (ecalPt ((lam : ℂ) * I) (ecalCoord ((lam : ℂ) * I) ζ)).im < 0 :=
    Approx.ecalPt_im_neg_of_sinh_im_pos lam _ hlam hwim hcosh
  rwa [hpt] at h1

/-! ## The main estimate -/

private theorem approxEcal_end_in_imag_neg_small_aux (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a κ ζ : ℂ), a ≠ 0 → ‖κ‖ ≤ K → ζ.re < 0 → ζ.im < 0 →
      ‖ζ‖ ≤ 4 → 4 * ‖a‖ ≤ ‖ζ‖ →
      0 < (Complex.sinh (a * ecalCoord a ζ) / a).im →
      ‖approxEcal a κ (ecalCoord a ζ + Real.pi * I / a)
        - (Real.pi * I / a - Real.pi * I * κ + ((1 / ζ) - κ * Complex.log ζ))‖
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
  have hwimu : 0 < (Complex.sinh (a * u) / a).im := by rw [hudef]; exact hwim
  have hu_sub : ‖u - 1/ζ‖ ≤ 4/9 * ‖a‖^2/‖ζ‖^3 := by
    rw [hudef]; exact ecalCoord_sub_inv_le_small a ζ ha hζne haζ
  have hu_le : ‖u‖ ≤ 2/‖ζ‖ := by
    rw [hudef]; exact ecalCoord_norm_le_small a ζ ha hζne haζ
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
  have hwarg_gt : 0 < (Complex.sinh (a * u)/a).arg := by
    have h1 : 0 ≤ (Complex.sinh (a * u)/a).arg :=
      Complex.arg_nonneg_iff.mpr (le_of_lt hwimu)
    have h2 : (Complex.sinh (a * u)/a).arg ≠ 0 := by
      intro h
      have := (Complex.arg_eq_zero_iff.mp h).2
      linarith
    exact lt_of_le_of_ne h1 (Ne.symm h2)
  have hζarg_lt : ζ.arg < 0 := Complex.arg_neg_iff.mpr him
  have hargcond : (Complex.sinh (a * u)/a).arg + ζ.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [Set.mem_Ioc]
    refine ⟨?_, ?_⟩
    · have h1 := Complex.neg_pi_lt_arg ζ
      linarith
    · have h1 := Complex.arg_le_pi (Complex.sinh (a * u)/a)
      linarith
  have hlogmul := Complex.log_mul hw0 hζne hargcond
  have hlogrel : Complex.log (Complex.sinh (a * u)/a) + Complex.log ζ
      = Complex.log (Complex.cosh (a * u)) := by
    rw [← hlogmul, hwζ]
  have hlog : ‖Complex.log (Complex.sinh (a * u)/a) + Complex.log ζ‖
      ≤ 6 * ‖a‖^2/‖ζ‖^2 := by
    rw [hlogrel]
    have hL : ‖Complex.log (Complex.cosh (a * u))‖ ≤ 3/2 * ‖a * u‖^2 :=
      Lnorm_log_cosh_le hau
    have h2 : (3/2:ℝ) * ‖a * u‖^2 ≤ 6 * ‖a‖^2/‖ζ‖^2 := by
      calc (3/2:ℝ) * ‖a * u‖^2 ≤ (3/2) * (4 * ‖a‖^2/‖ζ‖^2) :=
            mul_le_mul_of_nonneg_left hau2 (by norm_num)
        _ = 6 * ‖a‖^2/‖ζ‖^2 := by ring
    linarith
  have hshift := Approx.approxEcal_shift_neg a κ u ha hwimu
  have hmain : approxEcal a κ (u + Real.pi * I / a)
      - (Real.pi * I / a - Real.pi * I * κ + (1/ζ - κ * Complex.log ζ))
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



/-- **The incoming end at small `‖ζ‖`, lower half-plane (the mirror of
`Work.PARIMPL2.approxEcal_end_in_small`).**  For the purely imaginary parameter `a = iλ`
(`λ > 0`, the implosion side), the Écalle coordinate `u = ecalCoord (iλ) ζ`, on the branch
`0 < Im (sinh (a·u)/a)` (which forces `ζ` into the lower half-plane), satisfies the *sum* form of
the incoming asymptotics with the *sharp* error `O(λ²/‖ζ‖³)` — valid for small `ζ`
(`‖ζ‖ ≤ 4`, `4λ ≤ ‖ζ‖`), where the delivered
`Work.Implosion.Approx.approxEcal_end_in_imaginary_neg` needs `1 ≤ ‖ζ‖` and gives `O(λ²/‖ζ‖²)`.

Companion of the delivered `Work.PARIMPL2.approxEcal_end_in_small` (upper branch
`Im (sinh (a·u)/a) < 0`, which forces `Im ζ > 0`).  Same proof with the other branch:
`Work.Implosion.Approx.approxEcal_shift_neg` in place of `approxEcal_shift`,
`ecalPt_im_neg_of_sinh_im_pos` in place of `ecalPt_im_pos_of_sinh_im_neg`, and the branch
identity `log (-ζ) = log ζ + iπ` on `Im ζ < 0`.  These three lemmas live in
`Submission/Work/Implosion/Approx/approxEcal_end_in_imaginary_neg.lean`. -/

theorem approxEcal_end_in_imag_neg_small (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : ℝ) (κ ζ : ℂ), 0 < lam → ‖κ‖ ≤ K → ζ.re < 0 →
      ‖ζ‖ ≤ 4 → 4 * lam ≤ ‖ζ‖ →
      0 < (Complex.sinh (((lam : ℂ) * I) * Work.Implosion.ecalCoord ((lam : ℂ) * I) ζ)
        / ((lam : ℂ) * I)).im →
      ‖Work.Implosion.approxEcal ((lam : ℂ) * I) κ
          (Work.Implosion.ecalCoord ((lam : ℂ) * I) ζ + Real.pi * I / ((lam : ℂ) * I))
        - (Real.pi * I / ((lam : ℂ) * I) - Real.pi * I * κ
           + ((1 / ζ) - κ * Complex.log ζ))‖
      ≤ C * lam ^ 2 / ‖ζ‖ ^ 3 := by
  obtain ⟨C, hC0, hC⟩ := approxEcal_end_in_imag_neg_small_aux K hK
  refine ⟨C, hC0, ?_⟩
  intro lam κ ζ hlam hκ hre hζle hlamζ hwim
  have ha : ((lam : ℂ) * I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hlam)) Complex.I_ne_zero
  have hnorma : ‖((lam : ℂ) * I)‖ = lam := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
    exact abs_of_pos hlam
  have him : ζ.im < 0 := im_neg_of_sinh_im_pos_small lam ζ hlam hre hζle hlamζ hwim
  have h4 : 4 * ‖((lam : ℂ) * I)‖ ≤ ‖ζ‖ := by rw [hnorma]; exact hlamζ
  have h := hC ((lam : ℂ) * I) κ ζ ha hκ hre him hζle h4 hwim
  rwa [hnorma] at h

end

end Work.PARIMPL2.Lavaurs
