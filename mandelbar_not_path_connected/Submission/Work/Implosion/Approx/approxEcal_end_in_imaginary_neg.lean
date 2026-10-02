import Mathlib
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Ecalle.ecallePt_eq_coth
import Submission.Work.Implosion.Approx.approxEcal_shift
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

Private copies of the helpers used by `Approx.approxEcal_end_out` and
`Approx.approxEcal_end_in` (they are `private` there, so they cannot be imported). -/

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

/-! ## The mirror branch facts

For the **lower** half-plane incoming end the branch condition is
`0 < Im (sinh (a·u)/a)`, so the shift `u ↦ u + πi/a` changes `log` by `−πi` and the
shift identity acquires a `−πiκ`.  The first two lemmas are the exact mirror images of
`Approx.log_neg_of_im_neg` and `Approx.approxEcal_shift`. -/

/-- On the upper half-plane, `log (-w) = log w − πi` for the principal branch. -/
theorem log_neg_of_im_pos (w : ℂ) (hw : 0 < w.im) :
    Complex.log (-w) = Complex.log w - (Real.pi : ℂ) * I := by
  rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hw]
  push_cast
  ring

/-- **The shift identity, opposite branch.**  If `Im (sinh (a·u)/a) > 0`, then
`Ũ(u + πi/a) = Ũ(u) + πi/a − πiκ`, the mirror of `Approx.approxEcal_shift`. -/
theorem approxEcal_shift_neg (a κ u : ℂ) (ha : a ≠ 0)
    (h : 0 < (Complex.sinh (a * u) / a).im) :
    approxEcal a κ (u + Real.pi * I / a)
      = approxEcal a κ u + Real.pi * I / a - Real.pi * I * κ := by
  have ha' : a * (Real.pi * I / a) = Real.pi * I := by
    field_simp
  have harg : a * (u + Real.pi * I / a) = a * u + Real.pi * I := by
    rw [mul_add, ha']
  have hsinh : Complex.sinh (a * u + Real.pi * I) = -Complex.sinh (a * u) :=
    sinh_add_pi_I (a * u)
  have hlog : Complex.log (-(Complex.sinh (a * u) / a))
      = Complex.log (Complex.sinh (a * u) / a) - Real.pi * I :=
    log_neg_of_im_pos _ h
  unfold approxEcal
  rw [harg, hsinh, neg_div, hlog]
  ring

/-- For the purely imaginary parameter `a = iλ` (`λ > 0`), the branch condition
`0 < Im (sinh (a·u)/a)` forces the Écalle point `ζ(u) = ecalPt a u` into the **lower**
half-plane.  Mirror of `Approx.ecalPt_im_pos_of_sinh_im_neg`: with `w = sinh (a·u)/a`
and `c = cosh (a·u)`, the identity `c² + λ²w² = 1` gives `c.re·c.im = −λ²·w.re·w.im`,
hence `c.im·w.re ≤ 0` (as `c.re > 0`), while `−c.re·w.im < 0`; so the numerator
`c.im·w.re − c.re·w.im` of `Im (c/w) = Im (ecalPt a u)` is negative. -/
theorem ecalPt_im_neg_of_sinh_im_pos (lam : ℝ) (u : ℂ) (hlam : 0 < lam)
    (h : 0 < (Complex.sinh (((lam : ℂ) * I) * u) / ((lam : ℂ) * I)).im)
    (hc : 0 < (Complex.cosh (((lam : ℂ) * I) * u)).re) :
    (ecalPt ((lam : ℂ) * I) u).im < 0 := by
  set a : ℂ := (lam : ℂ) * I with ha
  have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hlam
  set s : ℂ := Complex.sinh (a * u) with hs
  set w : ℂ := s / a with hw
  set c : ℂ := Complex.cosh (a * u) with hcdef
  have ha0 : a ≠ 0 := by rw [ha]; exact mul_ne_zero hlamC Complex.I_ne_zero
  -- `w ≠ 0` because `0 < Im w`, hence `s ≠ 0`.
  have hw0 : w ≠ 0 := by intro hz; rw [hz] at h; simp at h
  have hs0 : s ≠ 0 := by intro hz; exact hw0 (by rw [hw, hz, zero_div])
  -- `a * w = s` by construction.
  have haw : a * w = s := by rw [hw]; exact mul_div_cancel₀ s ha0
  -- The hyperbolic identity `c ^ 2 - s ^ 2 = 1`.
  have hcs : c ^ 2 - s ^ 2 = 1 := by rw [hcdef, hs]; exact Complex.cosh_sq_sub_sinh_sq (a*u)
  -- `a ^ 2 = -λ²` since `a = iλ`.
  have ha_sq : a ^ 2 = -((lam ^ 2 : ℝ) : ℂ) := by
    rw [ha, mul_pow, Complex.I_sq]; push_cast; ring
  -- Hence `c ^ 2 + λ² w ^ 2 = 1`.
  have hkey : c ^ 2 + ((lam ^ 2 : ℝ) : ℂ) * w ^ 2 = 1 := by
    have h1 := hcs
    rw [← haw, mul_pow, ha_sq] at h1
    linear_combination h1
  -- Taking imaginary parts: `2 C D + 2 λ² p q = 0`.
  have him : (c ^ 2).im + lam ^ 2 * (w ^ 2).im = 0 := by
    have h1 := congrArg Complex.im hkey
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.one_im, zero_mul, add_zero] at h1
    exact h1
  have himc : (c ^ 2).im = 2 * c.re * c.im := by simp [pow_two, Complex.mul_im]; ring
  have himw : (w ^ 2).im = 2 * w.re * w.im := by simp [pow_two, Complex.mul_im]; ring
  rw [himc, himw] at him
  -- `C D = -λ² p q`.
  have hCD : c.re * c.im = -(lam^2) * (w.re * w.im) := by linarith
  -- `D p ≤ 0`, since `C > 0` and `C (D p) = -λ² p² q ≤ 0`.
  have hDp : c.im * w.re ≤ 0 := by
    have hprod : c.re * (c.im * w.re) = -(lam^2 * (w.re^2 * w.im)) := by
      rw [show c.re * (c.im * w.re) = (c.re * c.im) * w.re by ring, hCD]; ring
    have hnn : c.re * (c.im * w.re) ≤ 0 := by
      rw [hprod]
      exact neg_nonpos.mpr (mul_nonneg (sq_nonneg lam)
        (mul_nonneg (sq_nonneg w.re) (le_of_lt h)))
    exact nonpos_of_mul_nonpos_right hnn hc
  -- And `-C q < 0`, so the numerator `D p - C q` is negative.
  have hneg : c.im * w.re - c.re * w.im < 0 := by
    have h2 : 0 < c.re * w.im := mul_pos hc h
    linarith
  -- Non-degeneracy `ecalE a u ≠ 1`, needed to apply the cotangent identity.
  have hcs_add : c + s = Complex.exp (a * u) := by rw [hcdef, hs]; exact Complex.cosh_add_sinh (a*u)
  have hEne1 : ecalE a u ≠ 1 := by
    intro hE
    have hE2 : ecalE a u = (c + s) ^ 2 := by
      rw [ecalE, mul_assoc, two_mul, Complex.exp_add, ← hcs_add]
      ring
    rw [hE2] at hE
    have h2 : 2 * s * (c + s) = 0 := by linear_combination hE - hcs
    rcases mul_eq_zero.mp h2 with h4 | h4
    · rcases mul_eq_zero.mp h4 with h5 | h5
      · norm_num at h5
      · exact hs0 h5
    · exact Complex.exp_ne_zero (a*u) (by rw [← hcs_add]; exact h4)
  -- `ecalPt a u = c / w`, the closed cotangent form.
  have hpt : ecalPt a u = c / w := by
    have h1 := Ecalle.ecallePt_eq_coth a u hEne1
    rw [h1, coth, ← hcdef, ← hs, hw]
    field_simp
  have hdiv : (c / w).im = (c.im * w.re - c.re * w.im) / Complex.normSq w := by
    rw [Complex.div_im, ← sub_div]
  have hnorm : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw0
  calc (ecalPt a u).im = (c / w).im := by rw [hpt]
    _ = (c.im * w.re - c.re * w.im) / Complex.normSq w := hdiv
    _ < 0 := div_neg_of_neg_of_pos hneg hnorm

/-! ## Reusable pieces of the incoming-end estimate -/

/-- `‖ecalCoord a ζ‖ ≤ 2/‖ζ‖` in the regime `‖ζ‖ ≥ 1`, `4‖a‖ ≤ ‖ζ‖`, `‖a‖ ≤ 1`. -/
private lemma norm_ecalCoord_le (a ζ : ℂ) (ha : a ≠ 0) (hζ : 1 ≤ ‖ζ‖)
    (haζ : 4 * ‖a‖ ≤ ‖ζ‖) (ha1 : ‖a‖ ≤ 1) :
    ‖ecalCoord a ζ‖ ≤ 2 / ‖ζ‖ := by
  have hζpos : 0 < ‖ζ‖ := lt_of_lt_of_le zero_lt_one hζ
  have hu_sub : ‖ecalCoord a ζ - 1 / ζ‖ ≤ 4 / 9 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 :=
    ecalCoord_sub_inv_le a ζ ha hζ haζ
  have h1 : ‖ecalCoord a ζ‖ ≤ ‖ecalCoord a ζ - 1 / ζ‖ + ‖(1 : ℂ) / ζ‖ := by
    calc ‖ecalCoord a ζ‖ = ‖(ecalCoord a ζ - 1 / ζ) + 1 / ζ‖ := by ring_nf
      _ ≤ ‖ecalCoord a ζ - 1 / ζ‖ + ‖1 / ζ‖ := norm_add_le _ _
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
  have hfin : ‖ecalCoord a ζ‖ ≤ 1 / ‖ζ‖ + 1 / ‖ζ‖ := by linarith
  calc ‖ecalCoord a ζ‖ ≤ 1 / ‖ζ‖ + 1 / ‖ζ‖ := hfin
    _ = 2 / ‖ζ‖ := by ring

/-- `‖a * ecalCoord a ζ‖ ≤ 1/2` in the same regime, so that `cosh (a·u)` has positive
real part and `‖log (cosh (a·u))‖ ≤ (3/2)‖a·u‖²`. -/
private lemma norm_a_mul_ecalCoord_le_half (a ζ : ℂ) (ha : a ≠ 0) (hζ : 1 ≤ ‖ζ‖)
    (haζ : 4 * ‖a‖ ≤ ‖ζ‖) (ha1 : ‖a‖ ≤ 1) :
    ‖a * ecalCoord a ζ‖ ≤ 1 / 2 := by
  have hζpos : 0 < ‖ζ‖ := lt_of_lt_of_le zero_lt_one hζ
  have hu_le : ‖ecalCoord a ζ‖ ≤ 2 / ‖ζ‖ := norm_ecalCoord_le a ζ ha hζ haζ ha1
  have hau_le : ‖a * ecalCoord a ζ‖ ≤ 2 * ‖a‖ / ‖ζ‖ := by
    rw [norm_mul]
    calc ‖a‖ * ‖ecalCoord a ζ‖ ≤ ‖a‖ * (2 / ‖ζ‖) :=
          mul_le_mul_of_nonneg_left hu_le (norm_nonneg _)
      _ = 2 * ‖a‖ / ‖ζ‖ := by ring
  have h1 : ‖a‖ / ‖ζ‖ ≤ 1 / 4 := by rw [div_le_iff₀ hζpos]; linarith
  have h2 : 2 * ‖a‖ / ‖ζ‖ ≤ 1 / 2 := by rw [mul_div_assoc]; linarith
  linarith

/-- `ζ = ecalPt a (ecalCoord a ζ)` in the regime `4‖a‖ ≤ ‖ζ‖`, `a ≠ 0`. -/
private lemma ecalPt_ecalCoord_of_far (a ζ : ℂ) (ha : a ≠ 0) (hna : 0 < ‖a‖)
    (haζ : 4 * ‖a‖ ≤ ‖ζ‖) :
    ecalPt a (ecalCoord a ζ) = ζ := by
  have hlt : ‖a‖ < ‖ζ‖ := by linarith
  refine ecalPt_ecalCoord a ζ ha ?_ ?_
  · intro h; rw [h] at hlt; exact absurd hlt (lt_irrefl ‖a‖)
  · intro h; rw [h, norm_neg] at hlt; exact absurd hlt (lt_irrefl ‖a‖)

/-! ## The incoming-end estimate, opposite branch -/

/-- **The incoming end, opposite branch.**  For `ζ` in the open lower half-plane
(`Re ζ < 0`, `Im ζ < 0`) and the branch condition `0 < Im (sinh (a·u)/a)` at
`u = ecalCoord a ζ`, the chart at the shifted point satisfies

  `Ũ(u + πi/a) = πi/a − πiκ + 1/ζ − κ log ζ + O(‖a‖²/‖ζ‖²)`,

with constant `4/9 + 6K`.  This is the mirror of `Approx.approxEcal_end_in_im_pos`; the
logarithm identity `log (sinh (a·u)/a) + log ζ = log (cosh (a·u))` holds with no branch
ambiguity because `arg w ∈ (0, π)` and `arg ζ ∈ (−π, 0)`, so `arg w + arg ζ ∈ (−π, π)`
and Mathlib's `Complex.log_mul` applies. -/
private lemma approxEcal_end_in_im_neg_aux (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a κ ζ : ℂ), a ≠ 0 → ζ.re < 0 → ζ.im < 0 → 1 ≤ ‖ζ‖ → ‖κ‖ ≤ K →
      (Complex.sinh (a * ecalCoord a ζ) / a).im > 0 →
      4 * ‖a‖ ≤ ‖ζ‖ → ‖a‖ ≤ 1 →
      ‖approxEcal a κ (ecalCoord a ζ + Real.pi * I / a)
          - (Real.pi * I / a - Real.pi * I * κ + ((1 / ζ) - κ * Complex.log ζ))‖
        ≤ C * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by
  refine ⟨4 / 9 + 6 * K, by linarith, ?_⟩
  intro a κ ζ ha hre him hζ hκ hIm haζ ha1
  have hζpos : 0 < ‖ζ‖ := lt_of_lt_of_le zero_lt_one hζ
  have hζne : ζ ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hζpos)
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  set u : ℂ := ecalCoord a ζ with hu
  have hwu : 0 < (Complex.sinh (a * u) / a).im := by rw [hu]; exact hIm
  -- (β) the Écalle coordinate is `1/ζ` to second order
  have hu_sub : ‖u - 1 / ζ‖ ≤ 4 / 9 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by
    rw [hu]; exact ecalCoord_sub_inv_le a ζ ha hζ haζ
  -- (γ) hence `u` is small, of size `1/‖ζ‖`
  have hu_le : ‖u‖ ≤ 2 / ‖ζ‖ := by
    rw [hu]; exact norm_ecalCoord_le a ζ ha hζ haζ ha1
  have hau_le : ‖a * u‖ ≤ 2 * ‖a‖ / ‖ζ‖ := by
    rw [norm_mul]
    calc ‖a‖ * ‖u‖ ≤ ‖a‖ * (2 / ‖ζ‖) := mul_le_mul_of_nonneg_left hu_le (norm_nonneg _)
      _ = 2 * ‖a‖ / ‖ζ‖ := by ring
  have hau : ‖a * u‖ ≤ 1 / 2 := by
    rw [hu]; exact norm_a_mul_ecalCoord_le_half a ζ ha hζ haζ ha1
  have hau2 : ‖a * u‖ ^ 2 ≤ 4 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by
    calc ‖a * u‖ ^ 2 ≤ (2 * ‖a‖ / ‖ζ‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hau_le 2
      _ = 4 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by ring
  -- the correction `w = sinh (a·u)/a` is nonzero
  set w : ℂ := Complex.sinh (a * u) / a with hw
  have hwim : 0 < w.im := by rw [hw]; exact hwu
  have hwne : w ≠ 0 := by
    intro h
    have : w.im = 0 := by rw [h]; simp
    linarith [hwim, this]
  have hsinh_ne : Complex.sinh (a * u) ≠ 0 := by
    intro h
    exact hwne (by rw [hw, h, zero_div])
  have hEne : ecalE a u ≠ 1 := by
    intro h
    refine hsinh_ne (sinh_eq_zero_of_exp_two_mul_eq_one (a * u) ?_)
    rw [ecalE] at h
    rw [show (2 : ℂ) * (a * u) = 2 * a * u by ring]
    exact h
  -- the exact identity `w · ζ = cosh (a·u)`
  have hpt : ecalPt a u = ζ := by
    rw [hu]; exact ecalPt_ecalCoord_of_far a ζ ha hna haζ
  have hcoth : ecalPt a u = a * coth (a * u) := Ecalle.ecallePt_eq_coth a u hEne
  have hζeq : ζ = a * (Complex.cosh (a * u) / Complex.sinh (a * u)) := by
    rw [← hpt, hcoth, coth]
  have hmul : ζ * Complex.sinh (a * u) = a * Complex.cosh (a * u) := by
    rw [hζeq]; field_simp; try ring
  have hid : w * ζ = Complex.cosh (a * u) := by
    rw [hw, div_mul_eq_mul_div, mul_comm (Complex.sinh (a * u)) ζ, hmul,
      mul_div_cancel_left₀ _ ha]
  -- the argument condition, and the logarithmic identity
  have hargw : 0 < w.arg := by
    have h3 : 0 ≤ w.arg := Complex.arg_nonneg_iff.mpr (le_of_lt hwim)
    have h4 : w.arg ≠ 0 := by
      intro h
      exact absurd (Complex.arg_eq_zero_iff.mp h).2 (ne_of_gt hwim)
    exact lt_of_le_of_ne h3 (Ne.symm h4)
  have hargz : ζ.arg < 0 := Complex.arg_neg_iff.mpr him
  have hargsum : w.arg + ζ.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    rw [Set.mem_Ioc]
    have h1 := Complex.neg_pi_lt_arg ζ
    have h2 := Complex.arg_le_pi w
    constructor <;> linarith
  have hlogmul : Complex.log (w * ζ) = Complex.log w + Complex.log ζ :=
    Complex.log_mul hwne hζne hargsum
  have hlogrel : Complex.log w + Complex.log ζ = Complex.log (Complex.cosh (a * u)) := by
    rw [← hlogmul, hid]
  -- assembly
  have hshift : approxEcal a κ (u + Real.pi * I / a)
      = approxEcal a κ u + Real.pi * I / a - Real.pi * I * κ :=
    approxEcal_shift_neg a κ u ha hwu
  have hmain : approxEcal a κ (u + Real.pi * I / a)
      - (Real.pi * I / a - Real.pi * I * κ + (1 / ζ - κ * Complex.log ζ))
      = (u - 1 / ζ) + κ * (Complex.log w + Complex.log ζ) := by
    rw [hshift, approxEcal_apply, hw]
    ring
  rw [hmain]
  have hstep1 : ‖(u - 1 / ζ) + κ * (Complex.log w + Complex.log ζ)‖
      ≤ ‖u - 1 / ζ‖ + ‖κ‖ * ‖Complex.log w + Complex.log ζ‖ := by
    calc ‖(u - 1 / ζ) + κ * (Complex.log w + Complex.log ζ)‖
        ≤ ‖u - 1 / ζ‖ + ‖κ * (Complex.log w + Complex.log ζ)‖ := norm_add_le _ _
      _ = ‖u - 1 / ζ‖ + ‖κ‖ * ‖Complex.log w + Complex.log ζ‖ := by rw [norm_mul]
  have hstep2 : ‖κ‖ * ‖Complex.log w + Complex.log ζ‖ ≤ K * (6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2) := by
    have h1 : ‖Complex.log w + Complex.log ζ‖ ≤ 3 / 2 * ‖a * u‖ ^ 2 := by
      rw [hlogrel]; exact norm_log_cosh_le hau
    have h2 : (3 / 2 : ℝ) * ‖a * u‖ ^ 2 ≤ 6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by
      calc (3 / 2 : ℝ) * ‖a * u‖ ^ 2 ≤ (3 / 2) * (4 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hau2 (by norm_num)
        _ = 6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by ring
    calc ‖κ‖ * ‖Complex.log w + Complex.log ζ‖
        ≤ K * ‖Complex.log w + Complex.log ζ‖ :=
          mul_le_mul_of_nonneg_right hκ (norm_nonneg _)
      _ ≤ K * (3 / 2 * ‖a * u‖ ^ 2) := mul_le_mul_of_nonneg_left h1 hK
      _ ≤ K * (6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hK
  calc ‖(u - 1 / ζ) + κ * (Complex.log w + Complex.log ζ)‖
      ≤ ‖u - 1 / ζ‖ + ‖κ‖ * ‖Complex.log w + Complex.log ζ‖ := hstep1
    _ ≤ 4 / 9 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 + K * (6 * ‖a‖ ^ 2 / ‖ζ‖ ^ 2) := add_le_add hu_sub hstep2
    _ = (4 / 9 + 6 * K) * ‖a‖ ^ 2 / ‖ζ‖ ^ 2 := by ring

/-- **The incoming end for `a = iλ`, lower half-plane** — mirror image of the already
proved `Work.Implosion.Approx.approxEcal_end_in_imaginary`.

For `a = iλ` the branch condition `Im (sinh (a·u)/a) < 0` forces the incoming point into
the upper half-plane; with the **opposite** sign, `0 < Im (sinh (a·u)/a)`, the incoming
point lies in the lower half-plane and the shift identity changes sign
(`Complex.arg_neg_eq_arg_sub_pi_of_im_pos`), so the chart at `ecalCoord a ζ + πi/a` is
`πi/a − πiκ + 1/ζ − κ log ζ` instead of `πi/a + πiκ + 1/ζ − κ log ζ`.  Together the two
statements cover the whole incoming petal `Re ζ < 0`.

Proof.  Two auxiliary statements are needed (the prover writes them): (i) for
`‖w‖ ≤ 1/2`, `‖log (cosh w)‖ ≤ 3/2 * ‖w‖^2` — available as a `private` helper in
`Submission/Work/Implosion/Approx/approxEcal_end_out.lean`, copy the proof; (ii) for
`Im w > 0`, `log (-w) = log w - πi`, i.e. the analogue of `log_neg_of_im_neg` in
`Approx.approxEcal_shift` using `Complex.arg_neg_eq_arg_sub_pi_of_im_pos`.

Then: `log (sinh (a·u)/a) + log ζ = log (cosh (a·u))` needs `w.arg + ζ.arg ∈ Ioc (−π) π`
with `w = sinh (a·u)/a`; here `w.arg ∈ (0, π)` (from `0 < Im w`) and
`ζ.arg ∈ (−π, −π/2)` (from `Re ζ < 0`, `Im ζ < 0`), so the side condition is automatic and
`Complex.log_mul` applies with no branch ambiguity; `ecalCoord_sub_inv_le` and (i) then
give the bound with `C = 4/9 + 6K`, exactly as in `Work.Implosion.Approx.approxEcal_end_in_im_pos`.

The hypothesis `Im ζ < 0` is *derived*: from `c² + λ²w² = 1` (with `c = cosh (a·u)`,
`a² = −λ²`) one gets `c.re·c.im = −λ²·w.re·w.im`, and `‖a·u‖ ≤ 1/2` gives `c.re > 0`, so
`Im ζ = (c.im·w.re − c.re·w.im)/‖w‖² ≤ −c.re·w.im/‖w‖² < 0` — the same algebra as the
already delegated `ecalPt_im_pos_of_sinh_im_neg`, with the signs reversed. -/
theorem approxEcal_end_in_imaginary_neg (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : ℝ) (κ ζ : ℂ), 0 < lam → ζ.re < 0 → 1 ≤ ‖ζ‖ → ‖κ‖ ≤ K →
      0 < (Complex.sinh (((lam : ℂ) * I) * ecalCoord ((lam : ℂ) * I) ζ)
        / ((lam : ℂ) * I)).im →
      4 * ‖((lam : ℂ) * I)‖ ≤ ‖ζ‖ → ‖((lam : ℂ) * I)‖ ≤ 1 →
      ‖approxEcal ((lam : ℂ) * I) κ
          (ecalCoord ((lam : ℂ) * I) ζ + Real.pi * I / ((lam : ℂ) * I))
          - (Real.pi * I / ((lam : ℂ) * I) - Real.pi * I * κ
             + ((1 / ζ) - κ * Complex.log ζ))‖
        ≤ C * ‖((lam : ℂ) * I)‖ ^ 2 / ‖ζ‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := approxEcal_end_in_im_neg_aux K hK
  refine ⟨C, hC0, ?_⟩
  intro lam κ ζ hlam hre hζ hκ hIm haζ ha1
  have ha0 : ((lam : ℂ) * I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hlam)) Complex.I_ne_zero
  have hna : 0 < ‖((lam : ℂ) * I)‖ := norm_pos_iff.mpr ha0
  -- the branch condition forces the incoming point into the lower half-plane
  have hhalf : ‖((lam : ℂ) * I) * ecalCoord ((lam : ℂ) * I) ζ‖ ≤ 1 / 2 :=
    norm_a_mul_ecalCoord_le_half _ ζ ha0 hζ haζ ha1
  have hcosh : 0 < (Complex.cosh (((lam : ℂ) * I) * ecalCoord ((lam : ℂ) * I) ζ)).re :=
    re_cosh_pos hhalf
  have hpt : ecalPt ((lam : ℂ) * I) (ecalCoord ((lam : ℂ) * I) ζ) = ζ :=
    ecalPt_ecalCoord_of_far _ ζ ha0 hna haζ
  have him : ζ.im < 0 := by
    have h1 := ecalPt_im_neg_of_sinh_im_pos lam (ecalCoord ((lam : ℂ) * I) ζ) hlam hIm hcosh
    rwa [hpt] at h1
  exact hC _ κ ζ ha0 hre him hζ hκ hIm haζ ha1

end Work.Implosion.Approx
