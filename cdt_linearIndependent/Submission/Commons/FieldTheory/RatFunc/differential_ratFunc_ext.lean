import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Derivation.DifferentialRing
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# A derivation on a rational function field is determined by its values on polynomials

Let `K` be a field and let `RatFunc K = K(X)` be the field of rational functions over `K`.  The
polynomials `K[X]` sit inside `K(X)` via `algebraMap (Polynomial K) (RatFunc K)`, and since `K(X)`
is the fraction field of `K[X]`, the image of this map generates `K(X)` as a field.

Because `K(X)` has characteristic zero, the constants of a derivation on it form a subfield, and
more concretely, for any `a b : K(X)` the quotient rule

`D (a / b) = b⁻¹ ^ 2 • (b • D a - a • D b)`

expresses `D (a / b)` in terms of `D a` and `D b`.  Writing an arbitrary `x : K(X)` as
`p / q` with `p q : K[X]` (possible by `RatFunc.induction_on`), we conclude that a derivation on
`K(X)` is completely determined by its values on `K[X]`.

The main consequence is `differential_ratFunc_ext`: two `Differential` structures on `RatFunc K`
whose derivations agree on the image of `Polynomial K` are equal.
-/

namespace Commons.FieldTheory.RatFunc

open scoped Differential

/-- Two derivations on the field of rational functions `K(X)` that agree on the image of the
polynomials `K[X]` are equal.  This is because every element of `K(X)` is a quotient `p / q` of
polynomials and the quotient rule expresses `D (p / q)` in terms of `D p` and `D q`.

The instances of `Algebra ℤ (RatFunc K)` are given explicitly: `RatFunc K` carries the canonical
`ℤ`-algebra structure both directly (as any ring) and through the polynomial algebra, and these
two are not syntactically equal, so their arguments must be fixed by hand. -/
theorem deriv_ext_of_deriv_algebraMap {K : Type*} [Field K] {d₁ d₂ : Differential (RatFunc K)}
    (h : ∀ p : Polynomial K,
      d₁.deriv (algebraMap (Polynomial K) (RatFunc K) p)
        = d₂.deriv (algebraMap (Polynomial K) (RatFunc K) p)) :
    d₁.deriv = d₂.deriv := by
  refine @Derivation.ext ℤ (RatFunc K) (RatFunc K) _ _ _
    (Ring.toIntAlgebra (RatFunc K)) _ _ d₁.deriv d₂.deriv ?_
  intro x
  -- Write `x = p / q` for polynomials `p q`, using that `K(X)` is the fraction field of `K[X]`.
  induction x using RatFunc.induction_on with
  | _ p q _ =>
    -- The quotient rule reduces both sides to expressions in `D p` and `D q`.
    have h₁ := @Derivation.leibniz_div ℤ _ (RatFunc K) _ _ (RatFunc K) _ _
      (Ring.toIntAlgebra (RatFunc K)) d₁.deriv
      (algebraMap (Polynomial K) (RatFunc K) p) (algebraMap (Polynomial K) (RatFunc K) q)
    have h₂ := @Derivation.leibniz_div ℤ _ (RatFunc K) _ _ (RatFunc K) _ _
      (Ring.toIntAlgebra (RatFunc K)) d₂.deriv
      (algebraMap (Polynomial K) (RatFunc K) p) (algebraMap (Polynomial K) (RatFunc K) q)
    rw [h₁, h₂, h p, h q]

/-- Two `Differential` structures on the field of rational functions `K(X)` whose derivations agree
on the image of `K[X]` are equal.  This holds because `K(X)` is generated as a field by the image
of `K[X]` and a derivation of a field is determined by its values on a generating set. -/
theorem differential_ratFunc_ext {K : Type*} [Field K] {d₁ d₂ : Differential (RatFunc K)}
    (h : ∀ p : Polynomial K,
      d₁.deriv (algebraMap (Polynomial K) (RatFunc K) p)
        = d₂.deriv (algebraMap (Polynomial K) (RatFunc K) p)) : d₁ = d₂ :=
  Differential.ext (deriv_ext_of_deriv_algebraMap h)

end Commons.FieldTheory.RatFunc