import Mathlib
import Submission.Work.PARIMPL2.Direct.ecalPt_norm_le_max

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

open Complex

/-- The squared modulus of the Écalle point map at the purely imaginary parameter
`a = iλ` (`λ > 0`):

  `‖ecalPt iλ u‖² = λ² · (cos²(λ Re u) + sinh²(λ Im u)) / (sin²(λ Re u) + sinh²(λ Im u))`.

Indeed `ecalPt a u = a·coth(a u)` (`Ecalle.ecallePt_eq_coth`), and with `w = a·u`
one has `w.re = -λ·Im u`, `w.im = λ·Re u`, so that the standard identities
`‖cosh w‖² = cos²(w.im) + sinh²(w.re)` and `‖sinh w‖² = sin²(w.im) + sinh²(w.re)`
(`EcalNorm.norm_sq_cosh`, `EcalNorm.norm_sq_sinh`) give the formula, using
`‖a‖ = λ`.  The hypothesis `ecalE a u ≠ 1` only removes the punctures, where both
sides have a pole. -/
theorem ecalPt_norm_sq_eq (lam : ℝ) (hlam : 0 < lam) (u : ℂ)
    (hE : Work.Implosion.ecalE ((lam : ℂ) * Complex.I) u ≠ 1) :
    ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ^ 2
      = lam ^ 2 * ((Real.cos (lam * u.re) ^ 2 + Real.sinh (lam * u.im) ^ 2) /
          (Real.sin (lam * u.re) ^ 2 + Real.sinh (lam * u.im) ^ 2)) := by
  set a : ℂ := (lam : ℂ) * Complex.I with ha
  set w : ℂ := a * u with hw
  have hw_re : w.re = -(lam * u.im) := by
    rw [hw, ha]
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hw_im : w.im = lam * u.re := by
    rw [hw, ha]
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hna : ‖a‖ = lam := by
    rw [ha, Complex.norm_mul, Complex.norm_I, mul_one, Complex.norm_real]
    exact abs_of_pos hlam
  have hnorm : ‖Work.Implosion.ecalPt a u‖ =
      lam * (‖Complex.cosh w‖ / ‖Complex.sinh w‖) := by
    rw [Work.Implosion.Ecalle.ecallePt_eq_coth a u hE, Work.Implosion.coth, ← hw]
    rw [Complex.norm_mul, Complex.norm_div, hna]
  have hcosh : ‖Complex.cosh w‖ ^ 2 =
      Real.cos (lam * u.re) ^ 2 + Real.sinh (lam * u.im) ^ 2 := by
    rw [Work.PARIMPL2.Direct.EcalNorm.norm_sq_cosh, hw_im, hw_re, Real.sinh_neg]
    ring
  have hsinh : ‖Complex.sinh w‖ ^ 2 =
      Real.sin (lam * u.re) ^ 2 + Real.sinh (lam * u.im) ^ 2 := by
    rw [Work.PARIMPL2.Direct.EcalNorm.norm_sq_sinh, hw_im, hw_re, Real.sinh_neg]
    ring
  rw [hnorm, mul_pow, div_pow, hcosh, hsinh]

end Work.PARIMPL2.Direct
