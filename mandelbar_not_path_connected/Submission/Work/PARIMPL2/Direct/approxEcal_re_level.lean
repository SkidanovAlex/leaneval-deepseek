import Mathlib
import Submission.Work.Implosion.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.PARIMPL2.Direct

/-- On the imaginary axis `a = i·λ`, the real part of the approximate perturbed Fatou
coordinate `ũ(u) = u + κ·log(sinh(a·u)/a)` is the "level" part `u.re + κ.re·log‖w‖` up
to an error `|κ.im|·π` coming from the imaginary part of the principal logarithm,
which is the argument of `w = sinh(a·u)/a`, bounded in absolute value by `π`. -/
theorem approxEcal_re_level (lam : ℝ) (κ u : ℂ) :
    |(Work.Implosion.approxEcal ((lam : ℂ) * Complex.I) κ u).re
      - (u.re + κ.re * Real.log ‖Complex.sinh (((lam : ℂ) * Complex.I) * u)
          / ((lam : ℂ) * Complex.I)‖)| ≤ |κ.im| * Real.pi := by
  rw [Work.Implosion.approxEcal_apply]
  set w := Complex.sinh (((lam : ℂ) * Complex.I) * u) / ((lam : ℂ) * Complex.I)
  have hre : (u + κ * Complex.log w).re = u.re + (κ.re * Real.log ‖w‖ - κ.im * w.arg) := by
    rw [Complex.add_re, Complex.mul_re, Complex.log_re, Complex.log_im]
  rw [hre]
  have h1 : u.re + (κ.re * Real.log ‖w‖ - κ.im * w.arg) - (u.re + κ.re * Real.log ‖w‖)
      = -(κ.im * w.arg) := by ring
  rw [h1, abs_neg, abs_mul]
  exact mul_le_mul_of_nonneg_left (Complex.abs_arg_le_pi w) (abs_nonneg κ.im)

end Work.PARIMPL2.Direct
