import Mathlib
import Submission.Work.Implosion.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- For a complex number `z`, the squared modulus of `sin z` equals
`sin(z.re)^2 + sinh(z.im)^2`. -/
lemma normSq_sin (z : ℂ) :
    Complex.normSq (Complex.sin z) = Real.sin z.re ^ 2 + Real.sinh z.im ^ 2 := by
  have hsin : Complex.sin z =
      ((Real.sin z.re * Real.cosh z.im : ℝ) : ℂ) +
        ((Real.cos z.re * Real.sinh z.im : ℝ) : ℂ) * Complex.I := by
    rw [Complex.sin_eq, ← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
      ← Complex.ofReal_sinh, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  rw [hsin, Complex.normSq_add_mul_I]
  have hcosh := Real.cosh_sq z.im
  have hsc := Real.sin_sq_add_cos_sq z.re
  nlinarith [hcosh, hsc]

theorem sinh_chart_norm (lam : ℝ) (u : ℂ) :
    ‖Complex.sinh (((lam : ℂ) * Complex.I) * u) / ((lam : ℂ) * Complex.I)‖ ^ 2
      = (Real.sin (lam * u.re) ^ 2 + Real.sinh (lam * u.im) ^ 2) / lam ^ 2 := by
  set w : ℂ := (lam : ℂ) * u with hw
  have hwre : w.re = lam * u.re := by rw [hw]; simp [Complex.mul_re]
  have hwim : w.im = lam * u.im := by rw [hw]; simp [Complex.mul_im]
  have harg : ((lam : ℂ) * Complex.I) * u = w * Complex.I := by rw [hw]; ring
  have hsinh : Complex.sinh (((lam : ℂ) * Complex.I) * u) = Complex.I * Complex.sin w := by
    rw [harg, Complex.sinh_mul_I]; ring
  rw [← Complex.normSq_eq_norm_sq, hsinh, Complex.normSq_div, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_I, Complex.normSq_ofReal, one_mul]
  rw [normSq_sin, hwre, hwim]
  ring

end Work.PARIMPL2.Direct
