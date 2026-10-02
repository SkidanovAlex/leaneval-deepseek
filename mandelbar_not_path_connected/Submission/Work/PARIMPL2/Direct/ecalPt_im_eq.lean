import Mathlib
import Submission.Work.Implosion.All
import Submission.Work.PARIMPL2.Direct.ecalPt_norm_le_max

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

open Complex

/-- `ecalPt a u = a·coth(a·u)` **without** the puncture hypothesis `e^{2au} ≠ 1`.

At a puncture `e^{2au} = 1` one has `sinh (a·u) = 0`, so both sides of the
identity are `0` (division by zero in `ℂ` gives `0`); elsewhere the identity is
`Work.Implosion.Ecalle.ecallePt_eq_coth`. -/
theorem ecalPt_eq_coth_unconditional (a u : ℂ) :
    Work.Implosion.ecalPt a u = a * Work.Implosion.coth (a * u) := by
  set w : ℂ := a * u with hw
  have hE : Work.Implosion.ecalE a u = Complex.exp (2 * w) := by
    rw [Work.Implosion.ecalE]
    congr 1
    rw [hw]
    ring
  have hexp : Complex.exp w ≠ 0 := Complex.exp_ne_zero w
  have hsub : Complex.exp (2 * w) - 1 = 2 * Complex.exp w * Complex.sinh w := by
    rw [Complex.sinh, Complex.exp_neg, two_mul, Complex.exp_add]
    field_simp
  have hadd : Complex.exp (2 * w) + 1 = 2 * Complex.exp w * Complex.cosh w := by
    rw [Complex.cosh, Complex.exp_neg, two_mul, Complex.exp_add]
    field_simp
  have hnum : (2 : ℂ) * Complex.exp w ≠ 0 :=
    mul_ne_zero (by norm_num) hexp
  rw [Work.Implosion.ecalPt, hE, hsub, hadd, Work.Implosion.coth, hw]
  rw [show a * (2 * Complex.exp w * Complex.cosh w)
        = (2 * Complex.exp w) * (a * Complex.cosh w) by ring]
  rw [mul_div_mul_left _ _ hnum]
  ring

theorem ecalPt_im_eq (lam : ℝ) (u : ℂ) (E : ℝ) (hE : E = Real.sin (lam * u.re) ^ 2 + Real.sinh (lam * u.im) ^ 2) :
    (Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u).im
      = -(lam * Real.sinh (lam * u.im) * Real.cosh (lam * u.im)) / E := by
  set a : ℂ := (lam : ℂ) * Complex.I with ha
  set η : ℝ := lam * u.im with hη
  set θ : ℝ := lam * u.re with hθ
  set w : ℂ := a * u with hw
  have hw_re : w.re = -η := by
    rw [hw, ha, hη]
    simp [Complex.mul_re, Complex.mul_im]
  have hw_im : w.im = θ := by
    rw [hw, ha, hθ]
    simp [Complex.mul_re, Complex.mul_im]
  -- the components of `cosh w` and `sinh w` give the numerator of `Re (coth w)`
  have hnum : (Complex.cosh w).re * (Complex.sinh w).re + (Complex.cosh w).im * (Complex.sinh w).im
      = -(Real.sinh η * Real.cosh η) := by
    rw [EcalNorm.cosh_re, EcalNorm.cosh_im, EcalNorm.sinh_re, EcalNorm.sinh_im, hw_re, hw_im,
      Real.cosh_neg, Real.sinh_neg]
    linear_combination (-(Real.sinh η * Real.cosh η)) * Real.sin_sq_add_cos_sq θ
  have hden : Complex.normSq (Complex.sinh w) = Real.sin θ ^ 2 + Real.sinh η ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, EcalNorm.norm_sq_sinh, hw_im, hw_re, Real.sinh_neg]
    ring
  have hZ : (Work.Implosion.coth w).re
      = -(Real.sinh η * Real.cosh η) / (Real.sin θ ^ 2 + Real.sinh η ^ 2) := by
    rw [Work.Implosion.coth, Complex.div_re, ← add_div, hnum, hden]
  have him : (Work.Implosion.ecalPt a u).im = lam * (Work.Implosion.coth w).re := by
    rw [ecalPt_eq_coth_unconditional a u, ← hw, Complex.mul_im, ha]
    simp [Complex.mul_re, Complex.mul_im]
  rw [him, hZ, hE]
  ring

end Work.PARIMPL2.Direct
