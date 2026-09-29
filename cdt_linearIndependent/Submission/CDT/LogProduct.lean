import Mathlib
import Submission.CDT.LogTranscendence

/-!
# The function-field Lindemann–Weierstrass theorem, weight two

`Submission.CDT.LogTranscendence` proves the weight-one statements: for a nonconstant
`f ∈ K(X)` there is no `g ∈ K(X)` with `dRat g = (dRat f)/f`; an element `ℓ` of a differential
field extension of `K(X)` with `ℓ' = (dRat f)/f` is transcendental over `K(X)`; and
`1, ℓ, …, ℓ^{n-1}` are `K(X)`-linearly independent.

The natural next layer — the one needed to discuss *products* of logarithms, as in the paper's
§"Products of two logarithms" — is that the product `ℓ₁·ℓ₂` of two such logarithms is **not** a
rational function.

The proof is a three-line computation.  Suppose `u·v = r₀ ∈ K(X)` with `u' = (dRat f)/f` and
`v' = (dRat g)/g`, `g` nonconstant.  Differentiating the relation gives
`u·(dRat g)/g + v·(dRat f)/f = dRat r₀`; multiplying by `v` and substituting `u·v = r₀` gives the
*quadratic* equation

`(dRat f)/f · v² - (dRat r₀) · v + r₀·(dRat g)/g = 0`

for `v` over `K(X)`.  Its leading coefficient `(dRat f)/f` is nonzero when `f` is nonconstant, so
`v` would be algebraic over `K(X)` — contradicting the weight-one theorem, which says that `v`
(like `u`) is transcendental.  So no such relation exists.

Note that no multiplicative-independence hypothesis is needed (nor available) here: the argument
uses only that the two logarithms are *individually* transcendental.
-/

noncomputable section

namespace Submission.CDT

open Polynomial

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
variable {L : Type*} [Field L] [Algebra (RatFunc K) L] [Differential (RatFunc K)]
  [Differential L] [DifferentialAlgebra (RatFunc K) L]

/-- **Weight-two function-field Lindemann–Weierstrass.**  Let `L` be a differential field
extension of `K(X)` whose derivation restricts to `dRat`.  Let `u, v ∈ L` have the logarithmic
derivatives of the nonconstant rational functions `f, g ∈ K(X)`.  Then the product `u·v` is not a
rational function. -/
theorem not_exists_mul_eq_algebraMap
    (hderiv : ∀ r : RatFunc K, Differential.deriv r = dRat r)
    (f g : RatFunc K) (hf : dRat f ≠ 0) (hg : dRat g ≠ 0)
    (u v : L) (hu : Differential.deriv u = algebraMap (RatFunc K) L (dRat f / f))
    (hv : Differential.deriv v = algebraMap (RatFunc K) L (dRat g / g)) :
    ¬ ∃ r₀ : RatFunc K, u * v = algebraMap (RatFunc K) L r₀ := by
  rintro ⟨r₀, hr₀⟩
  have htr : Transcendental (RatFunc K) v :=
    transcendental_of_deriv_eq_dRat_div hderiv g hg v hv
  have hf0 : f ≠ 0 := fun h => hf (by rw [h, dRat_zero])
  have hff : dRat f / f ≠ 0 := div_ne_zero hf hf0
  -- differentiate the relation `u * v = r₀`
  have hd : u * Differential.deriv v + v * Differential.deriv u
      = algebraMap (RatFunc K) L (dRat r₀) := by
    have h1 : Differential.deriv (u * v)
        = Differential.deriv (algebraMap (RatFunc K) L r₀) := by rw [hr₀]
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1
    rw [DifferentialAlgebra.deriv_algebraMap, hderiv r₀] at h1
    exact h1
  -- multiply by `v` and substitute `u * v = r₀`: a quadratic equation for `v` over `K(X)`
  have h4 : algebraMap (RatFunc K) L (dRat f / f) * v ^ 2
      - algebraMap (RatFunc K) L (dRat r₀) * v
      + algebraMap (RatFunc K) L r₀ * algebraMap (RatFunc K) L (dRat g / g) = 0 := by
    have hmul := congrArg (fun x : L => x * v) hd
    rw [hu, hv] at hmul
    have h3 : (u * v) * algebraMap (RatFunc K) L (dRat g / g)
        + algebraMap (RatFunc K) L (dRat f / f) * v ^ 2
        = algebraMap (RatFunc K) L (dRat r₀) * v := by
      calc (u * v) * algebraMap (RatFunc K) L (dRat g / g)
            + algebraMap (RatFunc K) L (dRat f / f) * v ^ 2
          = (u * algebraMap (RatFunc K) L (dRat g / g)
              + v * algebraMap (RatFunc K) L (dRat f / f)) * v := by ring
        _ = algebraMap (RatFunc K) L (dRat r₀) * v := hmul
    rw [hr₀] at h3
    linear_combination h3
  -- the quadratic has a nonzero leading coefficient, so `v` would be algebraic
  have hcoeff : (Polynomial.C (dRat f / f) * Polynomial.X ^ 2 - Polynomial.C (dRat r₀) * Polynomial.X
      + Polynomial.C (r₀ * (dRat g / g)) : Polynomial (RatFunc K)).coeff 2 = dRat f / f := by
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X]
    norm_num
  have hPne : (Polynomial.C (dRat f / f) * Polynomial.X ^ 2 - Polynomial.C (dRat r₀) * Polynomial.X
      + Polynomial.C (r₀ * (dRat g / g)) : Polynomial (RatFunc K)) ≠ 0 := by
    intro h
    have h2 : dRat f / f = 0 := by
      have h2' := congrArg (fun p : Polynomial (RatFunc K) => p.coeff 2) h
      rw [hcoeff] at h2'
      simpa using h2'
    exact hff h2
  have haev : (Polynomial.aeval v) (Polynomial.C (dRat f / f) * Polynomial.X ^ 2
      - Polynomial.C (dRat r₀) * Polynomial.X
      + Polynomial.C (r₀ * (dRat g / g)) : Polynomial (RatFunc K)) = 0 := by
    simp only [Polynomial.aeval_def, Polynomial.eval₂_add, Polynomial.eval₂_sub,
      Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_pow,
      map_mul]
    exact h4
  exact hPne ((transcendental_iff.mp htr) _ haev)

end Submission.CDT
