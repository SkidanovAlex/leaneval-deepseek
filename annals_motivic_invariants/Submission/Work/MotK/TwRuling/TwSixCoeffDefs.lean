import Mathlib
import Submission.Work.MotK.TwRule
import Submission.Work.MotK.KleinTwData
import Submission.Work.MotK.TwRuling.TwFivetenDefs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The degree-6 coefficient forms of `R₀(A + T·B)` (T-twisted ruling nonvanishing)

Vocabulary for the proof of `Work.MotK.TwRuling.sdW_kleinTwR_ne_zero`.

Let `R` be a commutative ring, `a b h : R`, and let

* `qA k := kleinTwRuleA a b h X k` and `qB k := kleinTwRuleB a b h X k` be the two ruling
  vectors evaluated on the *variables* `X 0, …, X 4` (quadratic forms in `MvPolynomial (Fin 5) R`),
  `k : Fin 5`;
* `coeffPoly a b h : Polynomial (MvPolynomial (Fin 5) R)` be the image of the cubic
  `kleinTwR0 a b h` under the substitution `z k ↦ C (qA k) + T·C (qB k)` (with `T = Polynomial.X`);
* `sdCoeff6 a b h j := (coeffPoly a b h).coeff j` — the **degree-6 form** which is the
  coefficient of `T^j` in `R₀(A + T·B)`.

For a twisted Klein point `κ : Fin 5 → R(E)` satisfying the five twisted Pfaffians, the ruling
point is `W k = A(κ) k + T·B(κ) k`, and the coefficients of the image of `R₀(W)` in the
polynomial ring `R(E)[T]` are `aeval κ (sdCoeff6 a b h j)`.  Hence `R₀(W) ≠ 0` as soon as *one* of
the four forms `sdCoeff6 a b h j` (`j = 0,…,3`) is outside the degree-6 part of the twisted
Pfaffian ideal — that is the content of
`Work.MotK.TwRuling.sexticTw_notMem_kernel`.

## What is needed about `sdCoeff6`

* **Homogeneity.** Each `sdCoeff6 a b h j` is homogeneous of degree `6` in the variables `X i`,
  because `qA k`, `qB k` are homogeneous of degree `2` (`kleinTwRuleA`/`kleinTwRuleB` are quadratic
  in the point) and `kleinTwR0` is a cubic form.  Route: the scaling characterisation of
  `MvPolynomial.IsHomogeneous` — substituting `X i ↦ C λ * X i` multiplies `qA k` by `λ²` and
  `qB k` by `λ²`, hence multiplies `coeffPoly` by `C (λ^6)`.
* **Non-membership in the twisted Pfaffian ideal `I₆`.**  Evaluate at the explicit graded point
  `z = (a·h·α, 0, a·h·α², b, b·h·α³)` with `α⁵ = -1/h²` in an algebraically closed field
  (`IsAlgClosed.exists_pow_nat_eq`).  It satisfies **all five** twisted Pfaffians identically
  (`p₀ … p₄`), and

  * `aeval z (sdCoeff6 a b h 3) = a⁹ α³ b⁸ h⁶ (27 a⁵ - 11 b⁵)`,
  * `aeval z (sdCoeff6 a b h 2) = a⁷ α b¹⁰ h⁵ (57 a⁵ - b⁵)`.

  Since `a b h α ≠ 0`, this gives `sdCoeff6 a b h 3 ∉ I₆` whenever `27 a⁵ ≠ 11 b⁵`; and if
  `27a⁵ = 11b⁵` then `57a⁵ ≠ b⁵` unless `600 = 0`, i.e. unless the characteristic is `2`, `3` or
  `5`.  In characteristic `3` we have `27a⁵ - 11b⁵ = b⁵ ≠ 0`; in characteristic `5` the vanishing
  of `27a⁵ - 11b⁵ = 2a⁵ - b⁵` would contradict `Work.MotK.TwCensus.GoodDiscNe` (which gives
  `a¹⁰ - 11a⁵b⁵ - b¹⁰ ≠ 0` and equals `-5a¹⁰` when `b⁵ = 2a⁵`).  **The only remaining case is
  characteristic `2` with `a⁵ = b⁵`.**
-/

set_option autoImplicit false

namespace Work.MotK.TwRuling

open MvPolynomial

variable (R : Type*) [CommRing R] (a b h : R)

/-- The first ruling vector `A(c) = dP_c(u₁)` evaluated on the variables `X i` of
`MvPolynomial (Fin 5) R`: a quadratic form. -/
noncomputable def qA : Fin 5 → MvPolynomial (Fin 5) R :=
  fun k => Work.MotK.kleinTwRuleA (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (fun i => MvPolynomial.X i) k

/-- The second ruling vector `B(c) = dP_c(u₂)` evaluated on the variables `X i` of
`MvPolynomial (Fin 5) R`: a quadratic form. -/
noncomputable def qB : Fin 5 → MvPolynomial (Fin 5) R :=
  fun k => Work.MotK.kleinTwRuleB (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
    (fun i => MvPolynomial.X i) k

/-- `R₀(A + T·B)`, as a polynomial in `T` with coefficients in `MvPolynomial (Fin 5) R`. -/
noncomputable def coeffPoly : Polynomial (MvPolynomial (Fin 5) R) :=
  Work.MotK.kleinTwR0 (Polynomial.C (MvPolynomial.C a)) (Polynomial.C (MvPolynomial.C b))
    (Polynomial.C (MvPolynomial.C h))
    (fun k => Polynomial.C (qA R a b h k) + Polynomial.X * Polynomial.C (qB R a b h k))

/-- The coefficient of `T^j` in `R₀(A + T·B)`: a form of degree `6` in the variables `X i`. -/
noncomputable def sdCoeff6 (j : ℕ) : MvPolynomial (Fin 5) R := (coeffPoly R a b h).coeff j

@[simp] theorem qA_apply (k : Fin 5) :
    qA R a b h k = Work.MotK.kleinTwRuleA (MvPolynomial.C a) (MvPolynomial.C b)
      (MvPolynomial.C h) (fun i => MvPolynomial.X i) k := rfl

@[simp] theorem qB_apply (k : Fin 5) :
    qB R a b h k = Work.MotK.kleinTwRuleB (MvPolynomial.C a) (MvPolynomial.C b)
      (MvPolynomial.C h) (fun i => MvPolynomial.X i) k := rfl

@[simp] theorem sdCoeff6_eq (j : ℕ) :
    sdCoeff6 R a b h j = (coeffPoly R a b h).coeff j := rfl

end Work.MotK.TwRuling
