import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Approx
import Submission.Work.Implosion.Approx.approxEcal_shift

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Approx

open Complex

set_option linter.unusedVariables false in
/-- Reflection identity for the approximate perturbed Fatou coordinate `Ũ(u) = u + κ·log(sinh(a·u)/a)`
at the purely imaginary parameter `a = iλ` (`λ > 0`). Reflecting the point `u ↦ -ū` (the
reflection across the imaginary axis of the `ζ`-plane corresponds, in the `u`-coordinate, to
`u ↦ -ū` followed by a half-turn `u ↦ u + πi/…`) conjugates `Ũ` up to an explicit correction:
`Ũ(-ū) = -conj(Ũ(u)) + 2κ·log(sinh(a·ū)/a) + κπi`. The hypothesis puts `sinh(a·ū)/a` in the
open lower half-plane, which is exactly the slit condition making `log` respect conjugation
(`log(-z) = log z + πi` there). -/
theorem approxEcal_reflect (lam : ℝ) (κ : ℝ) (u : ℂ) (hlam : 0 < lam)
    (h : (Complex.sinh (((lam : ℂ) * I) * (starRingEnd ℂ u)) / ((lam : ℂ) * I)).im < 0) :
    approxEcal ((lam : ℂ) * I) (κ : ℂ) (-(starRingEnd ℂ u))
      = - starRingEnd ℂ (approxEcal ((lam : ℂ) * I) (κ : ℂ) u)
        + 2 * (κ : ℂ) * Complex.log (Complex.sinh (((lam : ℂ) * I) * (starRingEnd ℂ u)) / ((lam : ℂ) * I))
        + (κ : ℂ) * Real.pi * I := by
  set a : ℂ := (lam : ℂ) * I with ha_def
  have hsa : starRingEnd ℂ a = -a := by
    rw [ha_def, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  -- `A = sinh(a·ū)/a` is the conjugate of `w = sinh(a·u)/a`.
  have hA : Complex.sinh (a * (starRingEnd ℂ u)) / a
      = starRingEnd ℂ (Complex.sinh (a * u) / a) := by
    have e1 : a * (starRingEnd ℂ u) = -(starRingEnd ℂ (a * u)) := by
      rw [map_mul, hsa]; ring
    rw [e1, Complex.sinh_neg, Complex.sinh_conj, map_div₀, hsa]
    ring
  -- `sinh(a·(-ū))/a = -A`.
  have hneg : Complex.sinh (a * (-(starRingEnd ℂ u))) / a
      = -(Complex.sinh (a * (starRingEnd ℂ u)) / a) := by
    have e2 : a * (-(starRingEnd ℂ u)) = starRingEnd ℂ (a * u) := by
      rw [map_mul, hsa]; ring
    rw [e2, Complex.sinh_conj, hA, map_div₀, hsa]
    ring
  -- `log (-A) = log A + πi` on the open lower half-plane.
  have hlogneg : Complex.log (-(Complex.sinh (a * (starRingEnd ℂ u)) / a))
      = Complex.log (Complex.sinh (a * (starRingEnd ℂ u)) / a) + (Real.pi : ℂ) * I :=
    log_neg_of_im_neg _ h
  -- `w` is not real (its imaginary part is `-A.im > 0`), so `log` commutes with conjugation.
  have hwarg : (Complex.sinh (a * u) / a).arg ≠ Real.pi := by
    intro hh
    have him : (Complex.sinh (a * u) / a).im = 0 := (Complex.arg_eq_pi_iff.mp hh).2
    have hAim : (Complex.sinh (a * (starRingEnd ℂ u)) / a).im
        = -(Complex.sinh (a * u) / a).im := by
      rw [hA, Complex.conj_im]
    rw [hAim, him] at h
    norm_num at h
  have hlogconj : Complex.log (Complex.sinh (a * (starRingEnd ℂ u)) / a)
      = starRingEnd ℂ (Complex.log (Complex.sinh (a * u) / a)) := by
    rw [hA, Complex.log_conj _ hwarg]
  -- conjugation of `Ũ(u)`.
  have hstar : starRingEnd ℂ (approxEcal a (κ : ℂ) u)
      = starRingEnd ℂ u + (κ : ℂ) * Complex.log (Complex.sinh (a * (starRingEnd ℂ u)) / a) := by
    rw [approxEcal_apply, map_add, map_mul, Complex.conj_ofReal, ← hlogconj]
  rw [hstar, approxEcal_apply, hneg, hlogneg]
  ring

end Work.Implosion.Approx
