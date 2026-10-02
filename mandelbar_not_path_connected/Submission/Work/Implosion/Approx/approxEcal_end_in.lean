import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Disp
import Submission.Work.Implosion.Approx
import Submission.Work.Implosion.Approx.approxEcal_shift
import Submission.Work.Implosion.Approx.ecalCoord_sub_inv_le
import Submission.Work.Implosion.Ecalle.ecallePt_eq_coth

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Approx

open Complex
open Work.Implosion

/-!
# The incoming end `ζ.re < 0` of the approximate Fatou coordinate

The outgoing end (`ζ.re > 0`) is `approxEcal_end_out`: there
`Ũ(u(ζ)) = 1/ζ − κ log ζ` to second order.  Here we treat the *incoming* end
`ζ.re < 0`, where the relevant point is the translate `u(ζ) + πi/a` of the
Écalle coordinate; by `approxEcal_shift` (which is exactly where the hypothesis
`(sinh (a·u)/a).im < 0` is used) the two statements coincide:

  `Ũ(u + πi/a) − (πi/a + πi κ + (1/ζ − κ log ζ)) = Ũ(u) − (1/ζ − κ log ζ)`.

So it remains to bound `Ũ(u) − (1/ζ − κ log ζ)`.  Writing
`w = sinh(a·u)/a = cosh(a·u)/ζ`, this quantity is
`(u − 1/ζ) + κ·(log w + log ζ)`, and

* `‖u − 1/ζ‖ ≤ (4/9)·‖a‖²/‖ζ‖²` is `ecalCoord_sub_inv_le`;
* `log w + log ζ = log (cosh (a·u))`, since `w.im < 0` forces `ζ.im > 0`
  (the only new ingredient on this side), so that `w` and `ζ` lie in the two
  half-planes `arg w ∈ (−π,0)` and `arg ζ ∈ (π/2, π)`, whose arguments add up
  inside `(−π, π]`; then `‖log (cosh (a·u))‖ ≤ (3/2)‖a·u‖²`.
-/

/-! ## Elementary `cosh`/`log` bounds near `0` -/

/-- `‖cosh w − 1‖ ≤ ‖w‖²` for `‖w‖ ≤ 1`. -/
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

/-! ## The imaginary part of `w = sinh (a·u)/a` -/

/-- For `a = iλ` (`λ > 0`) the imaginary part of `sinh z / a` is `−Re (sinh z)/λ`, and
writing `q = e^z` this is `−q.re·(1 − 1/‖q‖²)/(2λ)`. -/
private lemma sinh_div_im (lam : ℝ) (hlam : 0 < lam) (z : ℂ) :
    (Complex.sinh z / ((lam : ℂ) * I)).im
      = -(Complex.exp z).re * (1 - 1 / Complex.normSq (Complex.exp z)) / (2 * lam) := by
  have hstep : (Complex.sinh z / ((lam : ℂ) * I)).im = -(Complex.sinh z).re / lam := by
    rw [Complex.div_im]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.normSq_apply]
    have hl : lam ≠ 0 := ne_of_gt hlam
    field_simp
    ring
  rw [hstep, Complex.sinh, Complex.exp_neg]
  rw [Complex.div_re, Complex.sub_re, Complex.inv_re, Complex.sub_im, Complex.inv_im,
    Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply]; norm_num; field_simp; ring

/-! ## The sign of `Im ζ` from the sign of `Im (sinh (a·u)/a)` -/

/-- **On the incoming end `ζ.re < 0`, the condition `(sinh (a·u)/a).im < 0`
forces `ζ.im > 0`.**  Here `a = iλ` (`λ > 0`) and `u = ecalCoord a ζ`.

Writing `m = m_a(ζ) = (ζ+a)/(ζ−a)`, one has `a·u = log m / 2`, and with
`q = e^{a·u}` (so `q² = m`, `q.re > 0` because `m` is in the open lower half-plane
as `ζ.re < 0`, and `‖q‖² = ‖m‖`)

  `(sinh(a·u)/a).im = −q.re·(1 − 1/‖m‖)/(2λ)`,

so `(sinh(a·u)/a).im < 0` gives `‖m‖ > 1`.  Finally
`‖m‖² − 1 = 4λ·ζ.im/‖ζ−a‖²`, so `‖m‖ > 1` gives `ζ.im > 0`. -/
private lemma im_pos_of_sinh_im_neg (lam : ℝ) (hlam : 0 < lam) (ζ : ℂ) (hre : ζ.re < 0)
    (h : (Complex.sinh (((lam : ℂ) * I) * ecalCoord ((lam : ℂ) * I) ζ)
        / ((lam : ℂ) * I)).im < 0) :
    0 < ζ.im := by
  set a : ℂ := (lam : ℂ) * I with hadef
  have ha0 : a ≠ 0 := by
    rw [hadef]; simp [Complex.I_ne_zero]; exact_mod_cast ne_of_gt hlam
  set u : ℂ := ecalCoord a ζ with hudef
  have hu : a * u = Complex.log (mobius a ζ) / 2 := by
    rw [hudef, ecalCoord]; field_simp
  have ha_re : a.re = 0 := by rw [hadef]; simp [Complex.mul_re, Complex.I_re]
  have hz_a : ζ ≠ a := by intro hh; rw [hh, ha_re] at hre; exact absurd hre (lt_irrefl 0)
  have hz_na : ζ ≠ -a := by intro hh; rw [hh] at hre; simp [ha_re] at hre
  have hm0 : mobius a ζ ≠ 0 := (mobius_ne_zero_iff a ζ).mpr ⟨hz_na, hz_a⟩
  have hDa : ζ - a ≠ 0 := sub_ne_zero.mpr hz_a
  have hDpos : 0 < Complex.normSq (ζ - a) := by
    rw [Complex.normSq_eq_norm_sq]; exact pow_pos (norm_pos_iff.mpr hDa) 2
  have hmim : (mobius a ζ).im < 0 := by
    have hform : (mobius a ζ).im = 2 * lam * ζ.re / Complex.normSq (ζ - a) := by
      rw [hadef, mobius, Complex.div_im]
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [hform]
    exact div_neg_of_neg_of_pos (by nlinarith [hlam, hre]) hDpos
  have him : (Complex.log (mobius a ζ) / 2).im = (mobius a ζ).arg / 2 := by
    rw [Complex.div_im, Complex.log_im]
    simp only [Complex.normSq_apply]; norm_num; ring
  have hqpos : 0 < (Complex.exp (Complex.log (mobius a ζ) / 2)).re := by
    rw [Complex.exp_re]
    refine mul_pos (Real.exp_pos _) ?_
    apply Real.cos_pos_of_mem_Ioo
    rw [him, Set.mem_Ioo]
    exact ⟨by have := Complex.neg_pi_lt_arg (mobius a ζ); linarith,
      by have := Complex.arg_neg_iff.mpr hmim; linarith [Real.pi_pos]⟩
  have hq2 : (Complex.exp (Complex.log (mobius a ζ) / 2)) ^ 2 = mobius a ζ := by
    rw [pow_two, ← Complex.exp_add,
      show Complex.log (mobius a ζ) / 2 + Complex.log (mobius a ζ) / 2 = Complex.log (mobius a ζ)
        by ring, Complex.exp_log hm0]
  have hqnorm : Complex.normSq (Complex.exp (Complex.log (mobius a ζ) / 2)) = ‖mobius a ζ‖ := by
    rw [Complex.normSq_eq_norm_sq, ← norm_pow, hq2]
  have hqexp : Complex.exp (a * u) = Complex.exp (Complex.log (mobius a ζ) / 2) := by rw [hu]
  have hqpos' : 0 < (Complex.exp (a * u)).re := by rw [hqexp]; exact hqpos
  have hqnorm' : Complex.normSq (Complex.exp (a * u)) = ‖mobius a ζ‖ := by
    rw [hqexp]; exact hqnorm
  have hwim : (Complex.sinh (a * u) / a).im
      = -(Complex.exp (a * u)).re
        * (1 - 1 / Complex.normSq (Complex.exp (a * u))) / (2 * lam) := by
    rw [hadef]; exact sinh_div_im lam hlam ((lam:ℂ)*I * u)
  have hbound : 1 < ‖mobius a ζ‖ := by
    rw [hwim, hqnorm'] at h
    have hneg : (-(Complex.exp (a * u)).re * (1 - 1 / ‖mobius a ζ‖)) / (2 * lam) < 0 := h
    rcases div_neg_iff.mp hneg with ⟨_, h2⟩ | ⟨h1, _⟩
    · exfalso; linarith
    · rw [neg_mul] at h1
      have h3 : 0 < (Complex.exp (a * u)).re * (1 - 1 / ‖mobius a ζ‖) := neg_lt_zero.mp h1
      have h4 : 0 < 1 - 1 / ‖mobius a ζ‖ := pos_of_mul_pos_right h3 (le_of_lt hqpos')
      have h5 : 1 / ‖mobius a ζ‖ < 1 := by linarith
      exact (div_lt_one (norm_pos_iff.mpr hm0)).mp h5
  have hkey : Complex.normSq (mobius a ζ) - 1 = 4 * lam * ζ.im / Complex.normSq (ζ - a) := by
    rw [hadef] at hDa ⊢
    have hD' : Complex.normSq (ζ - (lam : ℂ) * Complex.I) ≠ 0 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hDa)
    have hk : Complex.normSq (ζ + (lam : ℂ) * Complex.I)
        - Complex.normSq (ζ - (lam : ℂ) * Complex.I) = 4 * lam * ζ.im := by
      rw [Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    rw [mobius, Complex.normSq_div, ← div_self hD', ← sub_div, hk]
  have hnormsq : 1 < Complex.normSq (mobius a ζ) := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [hbound]
  have hfin : 0 < 4 * lam * ζ.im / Complex.normSq (ζ - a) := by rw [← hkey]; linarith
  have h4 : 0 < 4 * lam * ζ.im := by
    rcases div_pos_iff.mp hfin with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd h2 (not_lt.mpr (le_of_lt hDpos))
  have h4l : (0:ℝ) < 4 * lam := by linarith
  rcases mul_pos_iff.mp (show 0 < (4*lam) * ζ.im by linarith) with ⟨_, hh⟩ | ⟨hh, _⟩
  · exact hh
  · linarith

/-! ## The logarithmic identity `log w + log ζ = log (cosh (a·u))` -/

/-- **`log (sinh (a·u)/a) + log ζ = log (cosh (a·u))`** on the incoming end
(`ζ.re < 0`, `ζ.im > 0`, `(sinh (a·u)/a).im < 0`, `a = iλ`, `λ > 0`).

Indeed `w := sinh(a·u)/a = cosh(a·u)/ζ`, so `wζ = cosh(a·u)`.  The hypothesis
`w.im < 0` gives `w.arg ∈ (−π,0)` and `ζ.re < 0`, `ζ.im > 0` give
`ζ.arg ∈ (π/2,π)`, so `w.arg + ζ.arg ∈ (−π,π]` and `Complex.log_mul` applies. -/
private lemma log_sinh_div_add_log (lam : ℝ) (hlam : 0 < lam) (ζ : ℂ) (hre : ζ.re < 0)
    (him : 0 < ζ.im)
    (hwim : (Complex.sinh (((lam : ℂ) * I) * ecalCoord ((lam : ℂ) * I) ζ)
        / ((lam : ℂ) * I)).im < 0) :
    Complex.log (Complex.sinh (((lam : ℂ) * I) * ecalCoord ((lam : ℂ) * I) ζ)
        / ((lam : ℂ) * I)) + Complex.log ζ
      = Complex.log (Complex.cosh (((lam : ℂ) * I) * ecalCoord ((lam : ℂ) * I) ζ)) := by
  set a : ℂ := (lam : ℂ) * I with hadef
  have ha0 : a ≠ 0 := by
    rw [hadef]; simp [Complex.I_ne_zero]; exact_mod_cast ne_of_gt hlam
  set u : ℂ := ecalCoord a ζ with hudef
  have hu : a * u = Complex.log (mobius a ζ) / 2 := by rw [hudef, ecalCoord]; field_simp
  have ha_re : a.re = 0 := by rw [hadef]; simp [Complex.mul_re, Complex.I_re]
  have hz_a : ζ ≠ a := by intro hh; rw [hh, ha_re] at hre; exact absurd hre (lt_irrefl 0)
  have hz_na : ζ ≠ -a := by intro hh; rw [hh] at hre; simp [ha_re] at hre
  have hζne : ζ ≠ 0 := by intro hh; rw [hh] at him; simp at him
  have hm0 : mobius a ζ ≠ 0 := (mobius_ne_zero_iff a ζ).mpr ⟨hz_na, hz_a⟩
  have hm1 : mobius a ζ ≠ 1 := by
    rw [mobius]
    intro hh
    have hden : ζ - a ≠ 0 := sub_ne_zero.mpr hz_a
    have heq : ζ + a = ζ - a := (div_eq_one_iff_eq hden).mp hh
    have : a = 0 := by linear_combination heq / 2
    exact ha0 this
  have hEne : ecalE a u ≠ 1 := by
    rw [ecalE]
    have h2 : (2:ℂ) * a * u = Complex.log (mobius a ζ) := by rw [mul_assoc, hu]; ring
    rw [h2, Complex.exp_log hm0]
    exact hm1
  have hsinh : Complex.sinh (a*u) ≠ 0 := by
    intro hh
    apply hEne
    rw [ecalE, show (2:ℂ)*a*u = (a*u) - (-(a*u)) by ring, Complex.exp_sub]
    have h1 : Complex.exp (a*u) = Complex.exp (-(a*u)) := by
      have hh' := hh
      rw [Complex.sinh] at hh'
      have h2 : Complex.exp (a*u) - Complex.exp (-(a*u)) = 0 := by
        have := hh'; field_simp at this; simpa using this
      linear_combination h2
    rw [h1]
    exact div_self (Complex.exp_ne_zero _)
  have hpt : ecalPt a u = ζ := by rw [hudef]; exact ecalPt_ecalCoord a ζ ha0 hz_a hz_na
  have hcoth : ecalPt a u = a * coth (a*u) := Ecalle.ecallePt_eq_coth a u hEne
  have hζeq : ζ = a * (Complex.cosh (a*u)/Complex.sinh (a*u)) := by rw [← hpt, hcoth, coth]
  have hmul : ζ * Complex.sinh (a*u) = a * Complex.cosh (a*u) := by
    rw [hζeq]; field_simp; try ring
  have hwζ : (Complex.sinh (a*u)/a)*ζ = Complex.cosh (a*u) := by
    rw [div_mul_eq_mul_div, mul_comm (Complex.sinh (a*u)) ζ, hmul, mul_div_cancel_left₀ _ ha0]
  have hwarg_lt : (Complex.sinh (a*u)/a).arg < 0 := Complex.arg_neg_iff.mpr hwim
  have hζarg_gt : Real.pi/2 < ζ.arg := by
    by_contra hcontra
    rw [not_lt] at hcontra
    rcases (Complex.arg_le_pi_div_two_iff.mp hcontra) with h' | h'
    · linarith [hre]
    · linarith [him]
  have hw0 : Complex.sinh (a*u)/a ≠ 0 := div_ne_zero hsinh ha0
  have hargcond : (Complex.sinh (a*u)/a).arg + ζ.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [Set.mem_Ioc]
    refine ⟨?_, ?_⟩
    · have h1 := Complex.neg_pi_lt_arg (Complex.sinh (a*u)/a); linarith [Real.pi_pos]
    · have h1 := hwarg_lt; have h2 := Complex.arg_le_pi ζ; linarith
  have hlogmul := Complex.log_mul hw0 hζne hargcond
  rw [← hlogmul, hwζ]

/-! ## The main estimate -/

theorem approxEcal_end_in (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : ℝ) (κ ζ : ℂ), 0 < lam → ζ.re < 0 → 1 ≤ ‖ζ‖ → ‖κ‖ ≤ K →
      (Complex.sinh (((lam : ℂ) * I) * ecalCoord ((lam : ℂ) * I) ζ) / ((lam : ℂ) * I)).im < 0 →
      4 * lam ≤ ‖ζ‖ → lam ≤ 1 →
      ‖approxEcal ((lam : ℂ) * I) κ (ecalCoord ((lam : ℂ) * I) ζ + Real.pi * I / ((lam : ℂ) * I))
          - (Real.pi * I / ((lam : ℂ) * I) + Real.pi * I * κ + ((1 / ζ) - κ * Complex.log ζ))‖
        ≤ C * lam ^ 2 / ‖ζ‖ ^ 2 := by
  refine ⟨4 / 9 + 6 * K, by linarith, ?_⟩
  intro lam κ ζ hlam hre hζ hκ hwim haζ hlam1
  set a : ℂ := (lam : ℂ) * I with hadef
  have ha0 : a ≠ 0 := by
    rw [hadef]; simp [Complex.I_ne_zero]; exact_mod_cast ne_of_gt hlam
  set u : ℂ := ecalCoord a ζ with hudef
  have hnorma : ‖a‖ = lam := by
    rw [hadef, norm_mul, Complex.norm_I, mul_one]
    rw [Complex.norm_real]; exact abs_of_pos hlam
  have hwim' : (Complex.sinh (a * u) / a).im < 0 := by rw [hudef]; exact hwim
  have hImpos : 0 < ζ.im := by
    rw [hudef] at hwim'
    exact im_pos_of_sinh_im_neg lam hlam ζ hre (by simpa [hadef] using hwim')
  -- the shift identifies the two ends
  have hshift := approxEcal_shift a κ u ha0 hwim'
  have hgoal : approxEcal a κ (u + Real.pi * I / a)
        - (Real.pi * I / a + Real.pi * I * κ + (1 / ζ - κ * Complex.log ζ))
      = approxEcal a κ u - (1 / ζ - κ * Complex.log ζ) := by
    rw [hshift]; ring
  rw [hgoal]
  -- the logarithmic identity
  have hlogeq : Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ
      = Complex.log (Complex.cosh (a * u)) := by
    rw [hudef]
    exact log_sinh_div_add_log lam hlam ζ hre hImpos (by simpa [hadef] using hwim)
  -- basic size facts
  have hζpos : 0 < ‖ζ‖ := lt_of_lt_of_le zero_lt_one hζ
  have hu_sub : ‖u - 1 / ζ‖ ≤ 4 / 9 * lam ^ 2 / ‖ζ‖ ^ 2 := by
    have := ecalCoord_sub_inv_le a ζ ha0 hζ (by rw [hnorma]; exact haζ)
    rw [← hudef, hnorma] at this
    exact this
  have hu_le : ‖u‖ ≤ 2 / ‖ζ‖ := by
    have h1 : ‖u‖ ≤ ‖u - 1 / ζ‖ + ‖(1 : ℂ) / ζ‖ := by
      calc ‖u‖ = ‖(u - 1 / ζ) + 1 / ζ‖ := by ring_nf
        _ ≤ ‖u - 1 / ζ‖ + ‖1 / ζ‖ := norm_add_le _ _
    have hnorm_inv : ‖(1 : ℂ) / ζ‖ = 1 / ‖ζ‖ := by rw [norm_div, norm_one]
    rw [hnorm_inv] at h1
    have hb2 : 4 / 9 * lam ^ 2 ≤ ‖ζ‖ := by
      have h9 : lam / 9 ≤ 1 := by linarith
      calc 4 / 9 * lam ^ 2 = (4 * lam) * (lam / 9) := by ring
        _ ≤ ‖ζ‖ * 1 := mul_le_mul haζ h9 (by positivity) (by positivity)
        _ = ‖ζ‖ := by ring
    have hb : 4 / 9 * lam ^ 2 / ‖ζ‖ ^ 2 ≤ 1 / ‖ζ‖ := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < ‖ζ‖ ^ 2)]
      have hsq : (1 / ‖ζ‖) * ‖ζ‖ ^ 2 = ‖ζ‖ := by
        rw [one_div, inv_mul_eq_iff_eq_mul₀ (ne_of_gt hζpos), sq]
      rw [hsq]; exact hb2
    have hfin : ‖u‖ ≤ 1 / ‖ζ‖ + 1 / ‖ζ‖ := by linarith
    calc ‖u‖ ≤ 1 / ‖ζ‖ + 1 / ‖ζ‖ := hfin
      _ = 2 / ‖ζ‖ := by ring
  have hau_le : ‖a * u‖ ≤ 2 * lam / ‖ζ‖ := by
    rw [norm_mul, hnorma]
    calc lam * ‖u‖ ≤ lam * (2 / ‖ζ‖) := mul_le_mul_of_nonneg_left hu_le (le_of_lt hlam)
      _ = 2 * lam / ‖ζ‖ := by ring
  have hau : ‖a * u‖ ≤ 1 / 2 := by
    have h1 : lam / ‖ζ‖ ≤ 1 / 4 := by rw [div_le_iff₀ hζpos]; linarith
    have h2 : 2 * lam / ‖ζ‖ ≤ 1 / 2 := by rw [mul_div_assoc]; linarith
    linarith
  have hau2 : ‖a * u‖ ^ 2 ≤ 4 * lam ^ 2 / ‖ζ‖ ^ 2 := by
    calc ‖a * u‖ ^ 2 ≤ (2 * lam / ‖ζ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hau_le 2
      _ = 4 * lam ^ 2 / ‖ζ‖ ^ 2 := by ring
  have hlog : ‖Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ‖
      ≤ 6 * lam ^ 2 / ‖ζ‖ ^ 2 := by
    rw [hlogeq]
    have hL : ‖Complex.log (Complex.cosh (a * u))‖ ≤ 3 / 2 * ‖a * u‖ ^ 2 :=
      norm_log_cosh_le hau
    have h2 : (3 / 2 : ℝ) * ‖a * u‖ ^ 2 ≤ 6 * lam ^ 2 / ‖ζ‖ ^ 2 := by
      calc (3 / 2 : ℝ) * ‖a * u‖ ^ 2 ≤ (3 / 2) * (4 * lam ^ 2 / ‖ζ‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hau2 (by norm_num)
        _ = 6 * lam ^ 2 / ‖ζ‖ ^ 2 := by ring
    linarith
  have hmain : approxEcal a κ u - (1 / ζ - κ * Complex.log ζ)
      = (u - 1 / ζ) + κ * (Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ) := by
    rw [approxEcal_apply]; ring
  rw [hmain]
  calc ‖(u - 1 / ζ) + κ * (Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ)‖
      ≤ ‖u - 1 / ζ‖ + ‖κ‖ * ‖Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ‖ := by
        calc ‖(u - 1 / ζ) + κ * (Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ)‖
            ≤ ‖u - 1 / ζ‖ + ‖κ * (Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ)‖ :=
              norm_add_le _ _
          _ = ‖u - 1 / ζ‖ + ‖κ‖ * ‖Complex.log (Complex.sinh (a * u) / a) + Complex.log ζ‖ := by
              rw [norm_mul]
    _ ≤ 4 / 9 * lam ^ 2 / ‖ζ‖ ^ 2 + K * (6 * lam ^ 2 / ‖ζ‖ ^ 2) :=
        add_le_add hu_sub (mul_le_mul hκ hlog (norm_nonneg _) hK)
    _ = (4 / 9 + 6 * K) * lam ^ 2 / ‖ζ‖ ^ 2 := by ring

end Work.Implosion.Approx
