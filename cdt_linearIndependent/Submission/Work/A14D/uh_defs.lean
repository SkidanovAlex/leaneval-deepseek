import Mathlib
import Submission.Work.A14.defs

/-!
# A14D — formal data for the holomorphic solution `u_h` at `x = 1`

The function `uh` of `Submission.Work.A14.defs` is the power series `Σ aₙ (1−z)ⁿ` with
`a = uhCoeff`.  Here we collect

* the formal power series `Puh = Σ aₙ Xⁿ`;
* the polynomial coefficients `Ap`, `Bp`, `Cp` of the operator obtained from the Zagier
  operator `LZ` after the substitution `z = 1 − w` (so that `LZ` becomes
  `A(w)·y'' + B(w)·y' + C(w)·y`);
* the function `G0` defined by the coefficient series near `0`, so that `uh = G0 ∘ (1 − ·)`.
-/

namespace Work.A14D

open PowerSeries

noncomputable section

/-- The formal power series `Σₙ aₙ Xⁿ` of the coefficients `uhCoeff` of `uh`. -/
def Puh : PowerSeries ℚ := PowerSeries.mk uhCoeff

/-- `A(w) = -8w + 17w² - 9w³`: the `y''`-coefficient of `LZ` after `z = 1 - w`. -/
def Ap : Polynomial ℚ :=
  Polynomial.C (-8) * Polynomial.X + Polynomial.C 17 * Polynomial.X ^ 2
    + Polynomial.C (-9) * Polynomial.X ^ 3

/-- `B(w) = -8 + 34w - 27w²`: the `y'`-coefficient of `LZ` after `z = 1 - w`. -/
def Bp : Polynomial ℚ :=
  Polynomial.C (-8) + Polynomial.C 34 * Polynomial.X + Polynomial.C (-27) * Polynomial.X ^ 2

/-- `C(w) = 6 - 9w`: the `y`-coefficient of `LZ` after `z = 1 - w`. -/
def Cp : Polynomial ℚ := Polynomial.C 6 + Polynomial.C (-9) * Polynomial.X

/-- The sum of the coefficient series near `0`: `G0 w = Σₙ aₙ wⁿ`. -/
def G0 (w : ℂ) : ℂ := ∑' n : ℕ, (uhCoeff n : ℂ) * w ^ n

@[simp] lemma coeff_Puh (n : ℕ) : PowerSeries.coeff n Puh = uhCoeff n := PowerSeries.coeff_mk n _

/-- `uh` is `G0` composed with `z ↦ 1 - z`. -/
lemma uh_eq_G0 : uh = fun z : ℂ => G0 (1 - z) := funext fun _ => rfl

end

end Work.A14D
