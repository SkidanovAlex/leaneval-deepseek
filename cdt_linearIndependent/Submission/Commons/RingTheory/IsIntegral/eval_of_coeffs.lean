import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Evaluation of a polynomial with integral coefficients at an integral element

If every coefficient of `p : A[X]` is integral over `R` and `x : A` is
integral over `R`, then `p.eval x` is integral over `R`.

This follows immediately from the fact that the integral elements of `A`
over `R` form an `R`-subalgebra (`integralClosure R A`): expanding
`p.eval x = ∑ n in p.support, p.coeff n * x ^ n`, each summand lies in the
integral closure since `B` is closed under multiplication and powers, and the
(finite) sum lies in `B` by closure under sums.
-/

namespace Commons.RingTheory.IsIntegral

open Polynomial
open scoped BigOperators

lemma eval_of_coeffs {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (p : A[X])
    (hp : ∀ n : ℕ, IsIntegral R (p.coeff n)) {x : A} (hx : IsIntegral R x) :
    IsIntegral R (p.eval x) := by
  let B : Subalgebra R A := integralClosure R A
  have hxB : x ∈ B := by
    exact (mem_integralClosure_iff (R := R) (A := A)).mpr hx
  have hc : ∀ n : ℕ, p.coeff n ∈ B := fun n =>
    (mem_integralClosure_iff (R := R) (A := A)).mpr (hp n)
  have hmem : p.eval x ∈ B := by
    rw [eval_eq_sum, Polynomial.sum_def]
    apply B.sum_mem
    intro n hn
    exact B.mul_mem (hc n) (B.pow_mem hxB n)
  exact (mem_integralClosure_iff (R := R) (A := A)).mp hmem

end Commons.RingTheory.IsIntegral