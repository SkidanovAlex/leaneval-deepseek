import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Approx

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Approx

open Complex

/-- `sinh (z + πi) = - sinh z`. -/
theorem sinh_add_pi_I (z : ℂ) : Complex.sinh (z + (Real.pi : ℂ) * I) = -Complex.sinh z := by
  have hc : Complex.cosh ((Real.pi : ℂ) * I) = -1 :=
    (Complex.cosh_mul_I (Real.pi : ℂ)).trans Complex.cos_pi
  have hs : Complex.sinh ((Real.pi : ℂ) * I) = 0 := by
    rw [Complex.sinh_mul_I (Real.pi : ℂ), Complex.sin_pi]; simp
  rw [Complex.sinh_add, hc, hs]; ring

/-- On the lower half-plane, `log (-w) = log w + πi` for the principal branch. -/
theorem log_neg_of_im_neg (w : ℂ) (hw : w.im < 0) :
    Complex.log (-w) = Complex.log w + (Real.pi : ℂ) * I := by
  rw [Complex.log, Complex.log, norm_neg, Complex.arg_neg_eq_arg_add_pi_of_im_neg hw]
  push_cast
  ring

theorem approxEcal_shift (a κ u : ℂ) (ha : a ≠ 0)
    (h : (Complex.sinh (a * u) / a).im < 0) :
    approxEcal a κ (u + Real.pi * I / a) = approxEcal a κ u + Real.pi * I / a + Real.pi * I * κ := by
  have ha' : a * (Real.pi * I / a) = Real.pi * I := by
    field_simp
  have harg : a * (u + Real.pi * I / a) = a * u + Real.pi * I := by
    rw [mul_add, ha']
  have hsinh : Complex.sinh (a * u + Real.pi * I) = -Complex.sinh (a * u) :=
    sinh_add_pi_I (a * u)
  have hlog : Complex.log (-(Complex.sinh (a * u) / a))
      = Complex.log (Complex.sinh (a * u) / a) + Real.pi * I :=
    log_neg_of_im_neg _ h
  unfold approxEcal
  rw [harg, hsinh, neg_div, hlog]
  ring

end Work.Implosion.Approx
