import Mathlib
import Submission.CDT.RatFuncDeriv
import Submission.CDT.RatFuncConstants
import Submission.CDT.LogTranscendence

/-!
# The function-field Lindemann–Weierstrass theorem (logarithmic case), `f = 1 - y`

The classical function-field statement "`log f` is transcendental over `K` for a nonconstant `f`"
is the justification used in the paper (CDT, Lemma `seven`) for the `ℚ(x)`-independence of
`1, log(1−x), log²(1−x)`.

The general theorem is proved in `Submission.CDT.LogTranscendence`: for a nonconstant rational
function `f` over a field in which every nonconstant polynomial has a root, the logarithmic
derivative `(dRat f)/f` has a simple pole at every zero and pole of `f`, while `dRat g` never has
a simple pole (`ordAt_dRat_ne_neg_one`), so `(dRat f)/f` is not a derivative
(`not_exists_dRat_eq_dRat_div`); combined with the commons theorem
`Commons.FieldTheory.Differential.exists_deriv_of_deriv_eq_of_isAlgebraic` ("no new integration")
this makes `log f` transcendental over `ℂ(y)`
(`transcendental_of_deriv_eq_dRat_div`), and the powers `1, log f, …, log^{n-1} f` linearly
independent (`linearIndependent_powers_of_deriv_eq_dRat_div`).

This file records the special case `f = 1 - y` (`(log(1−y))' = −1/(1−y)`) in the names the rest of
the development uses.
-/

noncomputable section

namespace Submission.CDT

open Polynomial

/-- `y` as an element of `ℂ(y)`. -/
abbrev yC : RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X : Polynomial ℂ)

lemma one_sub_yC_eq : (1 : RatFunc ℂ) - yC
    = algebraMap (Polynomial ℂ) (RatFunc ℂ) (1 - Polynomial.X) := by
  rw [show yC = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.X : Polynomial ℂ) from rfl,
    ← map_one (algebraMap (Polynomial ℂ) (RatFunc ℂ)),
    ← map_sub (algebraMap (Polynomial ℂ) (RatFunc ℂ))]

lemma one_sub_X_ne_zero : (1 - Polynomial.X : Polynomial ℂ) ≠ 0 := by
  intro h
  have h1 : (1 - Polynomial.X : Polynomial ℂ).coeff 1 = -1 := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_X, ← Polynomial.C_1, Polynomial.coeff_C]
    norm_num
  rw [h] at h1
  norm_num at h1

lemma one_sub_X_natDegree : (1 - Polynomial.X : Polynomial ℂ).natDegree = 1 := by
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · refine le_trans (Polynomial.natDegree_sub_le (1 : Polynomial ℂ) Polynomial.X) ?_
    rw [Polynomial.natDegree_one, Polynomial.natDegree_X]
    norm_num
  · rw [Polynomial.coeff_sub, Polynomial.coeff_X, ← Polynomial.C_1, Polynomial.coeff_C]
    norm_num

/-- `dRat (1 - y) = -1`. -/
lemma dRat_one_sub_yC : dRat ((1 : RatFunc ℂ) - yC) = -1 := by
  rw [one_sub_yC_eq, dRat_algebraMap]
  simp [Polynomial.derivative_sub, Polynomial.derivative_X]

/-- `(log(1−y))' = -1/(1-y)` as a logarithmic derivative `(dRat f)/f`. -/
lemma dRat_one_sub_yC_div : dRat ((1 : RatFunc ℂ) - yC) / ((1 : RatFunc ℂ) - yC)
    = -(1 - yC)⁻¹ := by
  rw [dRat_one_sub_yC, neg_div, one_div]

/-- **`(log(1 − y))' = -1/(1-y)` is not a derivative in `ℂ(y)`.**  Special case `f = 1 - y` of
`not_exists_dRat_eq_dRat_div`. -/
theorem not_exists_dRat_eq_neg_inv_one_sub (g : RatFunc ℂ) :
    dRat g ≠ -(1 - yC)⁻¹ := by
  intro h
  refine not_exists_dRat_eq_dRat_div ((1 : RatFunc ℂ) - yC) (by rw [dRat_one_sub_yC]; norm_num)
    g ?_
  rw [h, dRat_one_sub_yC_div]

/-- **`log(1 − y)` is transcendental over `ℂ(y)`.**  Let `δ` be a derivation on `ℂ(y)` agreeing
with `dRat` (i.e. `δ = d/dy`), and let `L` be an extension field carrying a derivation extending
`δ`.  Then any `ℓ ∈ L` with `ℓ' = (log(1−y))' = -1/(1−y)` is transcendental over `ℂ(y)`.

This is the function-field Lindemann–Weierstrass theorem (logarithmic case) for `f = 1 - y`: the
logarithm of a nonconstant rational function is transcendental over the field of rational
functions.  (The `Differential (RatFunc ℂ)` instance is taken as a hypothesis together with its
compatibility with `dRat`, which avoids a `ℤ`-algebra diamond in `RatFunc ℂ`.) -/
theorem transcendental_of_deriv_eq_neg_inv_one_sub {L : Type*} [Field L]
    [Algebra (RatFunc ℂ) L] [Differential (RatFunc ℂ)]
    (hderiv : ∀ r : RatFunc ℂ, Differential.deriv r = dRat r)
    [Differential L] [DifferentialAlgebra (RatFunc ℂ) L] (ℓ : L)
    (hℓ : Differential.deriv ℓ = algebraMap (RatFunc ℂ) L (-(1 - yC)⁻¹)) :
    ¬ IsAlgebraic (RatFunc ℂ) ℓ := by
  refine transcendental_of_deriv_eq_dRat_div hderiv ((1 : RatFunc ℂ) - yC)
    (by rw [dRat_one_sub_yC]; norm_num) ℓ ?_
  rw [dRat_one_sub_yC_div]
  exact hℓ

/-- **The powers of `log(1 − y)` are `ℂ(y)`-linearly independent** — the shape in which the paper
(CDT, Lemma `seven`) uses the function-field Lindemann–Weierstrass theorem:
`1, log(1−y), …, log(1−y)^{n-1}` are linearly independent over `ℂ(y)`. -/
theorem linearIndependent_powers_of_deriv_eq_neg_inv_one_sub {L : Type*} [Field L]
    [Algebra (RatFunc ℂ) L] [Differential (RatFunc ℂ)]
    (hderiv : ∀ r : RatFunc ℂ, Differential.deriv r = dRat r)
    [Differential L] [DifferentialAlgebra (RatFunc ℂ) L] (ℓ : L)
    (hℓ : Differential.deriv ℓ = algebraMap (RatFunc ℂ) L (-(1 - yC)⁻¹)) (n : ℕ) :
    LinearIndependent (RatFunc ℂ) (fun i : Fin n => ℓ ^ (i : ℕ)) := by
  refine linearIndependent_powers_of_deriv_eq_dRat_div hderiv ((1 : RatFunc ℂ) - yC)
    (by rw [dRat_one_sub_yC]; norm_num) ℓ ?_ n
  rw [dRat_one_sub_yC_div]
  exact hℓ

end Submission.CDT
