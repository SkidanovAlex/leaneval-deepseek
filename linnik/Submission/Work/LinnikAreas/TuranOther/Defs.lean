import Mathlib
import Submission.Work.LinnikContract.Defs

/-!
# `Work.LinnikAreas.TuranOther.Defs`

Definitions for the Turán / Hadamard power-sum proof of the Deuring–Heilbronn phenomenon in the
**other-character** case (`Work.LinnikAreas.repelOtherNeDH`).

The argument (after Thorner–Zaman, arXiv:2208.11123, §"The Deuring–Heilbronn phenomenon",
following Kadiri–Ng–Wong, arXiv:1902.08640, §2) runs on the zero multiset of the twisted product

  `D(s) = ζ(s) · L(s,χ₀) · L(s+iγ,χ) · L(s+iγ,χ₀χ)`,

evaluated at the real point `s = 1 + α` with a fixed constant `α ≥ 1`: the *shift* by `iγ`
(the ordinate of the designated zero `ρ = β+iγ` of `L(·,χ)`) turns the complex point into a real
one, so that the whole power-sum machinery happens on the positive real axis.

If `ω` runs over all zeros of the four factors (the trivial zeros of each `L`-function included,
and the zeros of the level-correction factors of an imprimitive character), then the `j`-th power
sum of the quantities `z(ω) = (1+α-ω)^{-2}` satisfies

* (upper bound, from the Hadamard product of `D` and the non-negativity of the Dirichlet
  coefficients of `-D'/D`) `Re Σ_ω z(ω)^j ≤ 1/α^{2j} - (1+α-β₀)^{-2j}`,
* (lower bound, from Turán's power-sum method) `Re Σ_ω z(ω)^j ≥ (ε/(32+4ε))·|z(ω★)|^j` for some
  `j ≤ (8+ε)·Σ_ω ‖z(ω)‖/(‖z(ω★)‖+‖z(ω)‖)`, where `ω★` is the zero closest to `1+α`,

and the two together force `ω★` (hence every zero of every other character) to be repelled by the
exceptional zero `β₀`.

This file only fixes the notation: the multiplicities and the power sums.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators

noncomputable section

namespace Work.LinnikAreas.TuranOther

/-- The multiplicity of `u` as a zero of the Riemann zeta function (trivial zeros included). -/
def multZeta (u : ℂ) : ℕ := analyticOrderNatAt riemannZeta u

/-- The multiplicity of `u` as a zero of the (imprimitive) Dirichlet `L`-function of `χ`
(trivial zeros and the zeros of the level-correction factors included). -/
def multL {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (u : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) u

/-- The power-sum variable `z(u) = (1+α-u)^{-2}`. -/
def zval (α : ℝ) (u : ℂ) : ℂ := ((1 + (α : ℂ)) - u) ^ (-2 : ℤ)

/-- The multiplicity of `u` as a zero of the twisted product
`D(s) = ζ(s)·L(s,χ₀)·L(s+iγ,χ)·L(s+iγ,χ₀χ)`, with the point `0` and the exceptional zero `β₀`
removed (both are treated separately: `0` through the `s^{ord}` factor of the Hadamard product,
`β₀` by the extraction of the pole term `-(1+α-β₀)^{-2j}`).

The two `γ`-shifted families are indexed by the *unshifted* zero: the zero `ω` of `L(·,χ)`
appears as the entry `ω - iγ`, of multiplicity `multL χ ω`. -/
def twMult {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q) (β₀ γ : ℝ) (u : ℂ) : ℕ :=
  if u = 0 ∨ u = (β₀ : ℂ) then 0
  else multZeta u + multL χ₀ u + multL χ (u + Complex.I * (γ : ℂ))
      + multL (χ₀ * χ) (u + Complex.I * (γ : ℂ))

/-- The multiplicity-weighted `j`-th power sum over the twisted zero multiset. -/
def twSum {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q) (β₀ γ α : ℝ) (j : ℕ) : ℝ :=
  ∑' u : ℂ, ((twMult χ₀ χ β₀ γ u : ℕ) : ℝ) * (zval α u ^ j).re


/-- The Turán power-sum weight for the twisted product, extended by `0` off its zero multiset:
`twZ α u = zval α u` when `u` is a zero of `twMult`, and `0` otherwise.  It is the `z` of Turán's
theorem (`Work.LinnikAreas.DhK.turanWeighted`) in the application: the `0` extension makes
`‖twZ α ·‖` bounded, with the maximum attained on the zero multiset (`twMultMax`). -/
def twZ {q : ℕ} [NeZero q] (χ₀ χ : DirichletCharacter ℂ q) (β₀ γ α : ℝ) (u : ℂ) : ℂ :=
  if twMult χ₀ χ β₀ γ u = 0 then 0 else zval α u

end Work.LinnikAreas.TuranOther

end
