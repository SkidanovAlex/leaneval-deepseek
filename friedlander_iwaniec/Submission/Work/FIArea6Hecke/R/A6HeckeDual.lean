/-
# `Submission.Work.FIArea6Hecke.R.A6HeckeDual`

The **dual theta function** `thetaDual d chi w = Σ_ξ ĝ(ξ)·e^{-π|ξ|²w}` of a strict character `χ`
modulo `4d`, `ĝ(ξ) = gaussSum d χ ξ` the finite Fourier transform of `χ` on `ℤ[i]/(4d)`.

It is the dual of the spherical theta series `thetaOdd χ 0` under Poisson summation
(`thetaOdd_eq_poisson_form`): for `u > 0`

  `thetaOdd χ 0 u = (16d²u)^{-1}·thetaDual d χ (1/(16d²u))`,

and it is the function whose Mellin transform completes the "other side" of Hecke's functional
equation of the imprimitive character `χ`.  The point of splitting it out as a definition is that
the analytic properties needed for the analytic continuation of the completed Hecke `L`-function
(continuity on `(0,∞)`, exponential decay at `∞` when `gaussSum d χ 0 = 0`) can be stated about it
directly.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.ThetaDefs
import Submission.Work.FIArea5.S16Hecke.thetaOdd_poisson
import Submission.Work.FIArea5.S16Hecke.thetaOdd_eq_unitSum_mul_thetaHol

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators

noncomputable section

/-- **The dual theta function** `thetaDual d χ w = Σ_{ξ ∈ ℤ[i]} ĝ(ξ)·e^{-π|ξ|²w}`, written as a
sum over `ℤ × ℤ`, where `ĝ(ξ) = gaussSum d χ ξ` is the Gauss sum (finite Fourier transform) of the
strict character `χ`. -/
def thetaDual (d : ℕ) (chi : GaussianInt → ℂ) (w : ℝ) : ℂ :=
  ∑' ξ : ℤ × ℤ, Work.FIArea5.S16Hecke.gaussSum d chi ⟨ξ.1, ξ.2⟩ *
    Complex.exp (-Real.pi * (((ξ.1 : ℝ) ^ 2 + (ξ.2 : ℝ) ^ 2) * w))

end

end Work.FIArea6Hecke.R
