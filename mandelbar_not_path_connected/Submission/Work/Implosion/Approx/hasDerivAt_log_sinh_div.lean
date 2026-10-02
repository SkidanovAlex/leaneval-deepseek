import Mathlib
import Submission.Work.Implosion.Basic
import Submission.Work.Implosion.Ecalle
import Submission.Work.Implosion.Approx
import Submission.Work.Implosion.Ecalle.ecallePt_eq_coth

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion.Approx

open Complex

/-- `sinh w = 0` as soon as `e^{2w} = 1`.  (For complex `w` the converse of the
familiar real statement is what is true: `sinh w = 0 ↔ w ∈ πiℤ`, and `e^{2w} = 1`
is exactly the same condition.) -/
theorem sinh_eq_zero_of_exp_two_mul_eq_one (w : ℂ) (h : Complex.exp (2 * w) = 1) :
    Complex.sinh w = 0 := by
  have hsq : Complex.exp w ^ 2 = 1 := by
    have h2 : Complex.exp (2 * w) = Complex.exp w * Complex.exp w := by
      rw [two_mul, Complex.exp_add]
    rw [pow_two, ← h2]; exact h
  have hneg : Complex.exp (-w) = (Complex.exp w)⁻¹ := Complex.exp_neg w
  rw [Complex.sinh, hneg]
  rcases sq_eq_one_iff.mp hsq with h1 | h1
  · rw [h1]; norm_num
  · rw [h1, inv_neg, inv_one]; norm_num

/-- `d/du log (sinh (a·u)/a) = ζ(u) = a·coth(a·u)`, the Écalle point map.

This is the antiderivative identity used for the approximate perturbed Fatou
coordinate `Ũ(u) = u + κ·log(sinh(a·u)/a)`; it is the chain rule together with
the identification `ζ(u) = a·coth(a·u)` of `ecallePt_eq_coth`.  The hypothesis
that the argument of `log` lies in the slit plane is what makes the principal
branch of `log` differentiable there (it also rules out the punctures, where
`sinh(a·u) = 0` and `ζ` has a pole). -/
theorem hasDerivAt_log_sinh_div (a u : ℂ) (ha : a ≠ 0)
    (hslit : Complex.sinh (a * u) / a ∈ Complex.slitPlane) :
    HasDerivAt (fun v : ℂ => Complex.log (Complex.sinh (a * v) / a)) (ecalPt a u) u := by
  -- `sinh (a·u) ≠ 0`, hence the punctures `u ∈ (πi/a)ℤ` are avoided.
  have hsinh_ne : Complex.sinh (a * u) ≠ 0 := by
    intro h
    exact Complex.slitPlane_ne_zero hslit (by rw [h, zero_div])
  have hE_ne : ecalE a u ≠ 1 := by
    intro h
    refine hsinh_ne (sinh_eq_zero_of_exp_two_mul_eq_one (a * u) ?_)
    rw [show (2 : ℂ) * (a * u) = 2 * a * u by ring]; exact h
  -- Chain rule: derivative of `v ↦ sinh (a·v)/a` is `cosh (a·u)`.
  have hinner : HasDerivAt (fun v : ℂ => Complex.sinh (a * v) / a) (Complex.cosh (a * u)) u := by
    have h1 : HasDerivAt (fun v : ℂ => Complex.sinh (a * v)) (Complex.cosh (a * u) * a) u :=
      (Complex.hasDerivAt_sinh (a * u)).comp u (hasDerivAt_const_mul a)
    have h2 := h1.div_const a
    have h3 : Complex.cosh (a * u) * a / a = Complex.cosh (a * u) :=
      mul_div_cancel_right₀ _ ha
    rw [h3] at h2
    exact h2
  -- The value of the derivative is `a·coth(a·u) = ζ(u)`.
  have hval : (Complex.sinh (a * u) / a)⁻¹ * Complex.cosh (a * u) = ecalPt a u := by
    rw [Work.Implosion.Ecalle.ecallePt_eq_coth a u hE_ne, Work.Implosion.coth,
      inv_div, div_mul_eq_mul_div, mul_div_assoc]
  have hcomp := (Complex.hasDerivAt_log hslit).comp u hinner
  rw [hval] at hcomp
  exact hcomp

end Work.Implosion.Approx
