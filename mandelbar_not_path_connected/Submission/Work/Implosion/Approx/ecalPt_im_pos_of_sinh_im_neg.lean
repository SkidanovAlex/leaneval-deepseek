import Mathlib
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Ecalle.ecallePt_eq_coth

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Approx

open Complex

/-- For the purely imaginary parameter `a = iλ` (`λ > 0`), the branch condition
`Im (sinh (a·u)/a) < 0` forces the Écalle point `ζ(u) = ecalPt a u` into the **upper**
half-plane.  Proof sketch: with `w = sinh (a·u)/a` and `c = cosh (a·u)`, write
`c = C + iD`, `w = p + iq`; then `q < 0`, `C > 0` (hypotheses), `ecalPt a u = c/w`
(`Ecalle.ecallePt_eq_coth`), so `Im (ecalPt a u) = (D·p − C·q)/‖w‖²`, and from
`c² − (a·w)² = 1` with `a² = −λ²` we get `2·C·D = −2λ²·p·q`, i.e. `D·p ≥ 0`; hence
`D·p − C·q ≥ −C·q > 0`. -/
theorem ecalPt_im_pos_of_sinh_im_neg (lam : ℝ) (u : ℂ) (hlam : 0 < lam)
    (h : (Complex.sinh (((lam : ℂ) * I) * u) / ((lam : ℂ) * I)).im < 0)
    (hc : 0 < (Complex.cosh (((lam : ℂ) * I) * u)).re) :
    0 < (ecalPt ((lam : ℂ) * I) u).im := by
  set a : ℂ := (lam : ℂ) * I with ha
  have hlamC : (lam : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hlam
  set s : ℂ := Complex.sinh (a * u) with hs
  set w : ℂ := s / a with hw
  set c : ℂ := Complex.cosh (a * u) with hcdef
  have ha0 : a ≠ 0 := by rw [ha]; exact mul_ne_zero hlamC Complex.I_ne_zero
  -- `w ≠ 0` because `Im w < 0`, hence `s ≠ 0`.
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
  -- `D p ≥ 0`, since `C > 0` and `C (D p) = -λ² p² q ≥ 0`.
  have hDp : 0 ≤ c.im * w.re := by
    have hprod : c.re * (c.im * w.re) = -(lam^2 * (w.re^2 * w.im)) := by
      rw [show c.re * (c.im * w.re) = (c.re * c.im) * w.re by ring, hCD]; ring
    have hnn : 0 ≤ c.re * (c.im * w.re) := by
      rw [hprod]
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg lam)
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg w.re) (le_of_lt h)))
    exact nonneg_of_mul_nonneg_right hnn hc
  -- And `-C q > 0`, so the numerator `D p - C q` is positive.
  have hpos : 0 < c.im * w.re - c.re * w.im := by
    have h2 : c.re * w.im < 0 := mul_neg_of_pos_of_neg hc h
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
    _ > 0 := div_pos hpos hnorm

end Work.Implosion.Approx
