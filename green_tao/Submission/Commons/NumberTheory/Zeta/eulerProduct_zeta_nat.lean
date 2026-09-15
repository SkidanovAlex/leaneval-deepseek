import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

namespace Commons.NumberTheory.Zeta

open Complex Function

/-- The Euler product for the Riemann zeta function, indexed by the *natural numbers* (composite
indices contributing the neutral factor `1`), in the `HasProd` form:
for `Re s > 1`, `HasProd (fun p : ℕ => if p.Prime then (1 - p^{-s})⁻¹ else 1) (riemannZeta s)`.

Proof sketch: Mathlib has `riemannZeta_eulerProduct_hasProd (hs : 1 < s.re) :
HasProd (fun p : Primes => (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s)` (in
`Mathlib/NumberTheory/EulerProduct/DirichletLSeries.lean`).  Transport this along the equivalence
between `ℕ`-indexed products with `1` at the non-primes and `Primes`-indexed products: a useful
general form is `∏' n : ℕ, f n = ∏' n : {n // n.Prime}, f n` when `f n = 1` for all non-primes
(prove via `Multipliable`/`HasProd` over a subtype, e.g. `HasProd.subtype_mul`/`tprod_subtype` and
the fact that the family `fun n => f n` is multipliable, or via `hasProd_iff_tendsto` and
`Finset.prod_subset`).  Also useful: `Nat.Prime.not_prime`. -/
theorem eulerProduct_zeta_nat {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : ℕ => if p.Prime then (1 - (p : ℂ) ^ (-s))⁻¹ else 1) (riemannZeta s) := by
  have h := (hasProd_subtype_iff_mulIndicator (s := {n : ℕ | n.Prime})
      (f := fun n : ℕ => (1 - (n : ℂ) ^ (-s))⁻¹)).mp
        (riemannZeta_eulerProduct_hasProd hs)
  convert h using 1
  ext n
  simp [Set.mulIndicator]

end Commons.NumberTheory.Zeta