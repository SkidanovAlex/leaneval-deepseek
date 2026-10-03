import Mathlib
import Submission.Work.ORLyndon.powDefs
import Submission.Work.ORLyndon.Fox

/-!
# The Fox vector of a torus relator `x ^ p * y ^ q`

For the relator `r = (x ^ p * y ^ q) ^ l` of the two-generator torus presentation, the component of
the root Fox vector at the letter `x` is the `p`-term geometric sum in the class of `x`:

`(∂u/∂x)_x = 1 + x̄ + ⋯ + x̄ ^ (p - 1)`,  `u = x ^ p * y ^ q`, `x̄ = presentRho r x`.

The Fox calculus input is `foxD_letterPow_mul_letterPow`: the Leibniz rule `foxD_mul` splits
`∂ (x ^ p * y ^ q) / ∂x` into `∂ (x ^ p)/∂x + of (x ^ p) * ∂(y ^ q)/∂x`, the geometric-series identity
`foxD_pow` gives `∂(x ^ p)/∂x = ∑_{i < p} x ^ i` and `∂(y ^ q)/∂x = 0` since `y ≠ x`.  Pushing the
result along the presentation map `presentAlg` (`rootVec_apply`, `map_sum`, `map_pow`,
`presentAlg_of`) turns the free-group identity into the group-algebra identity of the statement.

This is the component computation used in the base case of the Cohen--Lyndon induction for the
Freiheitssatz example; it also feeds `Work.ORLyndon.annAt_letterPow_mul_letterPow`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

/-- The Fox derivative of a power of the differentiating letter itself is the geometric sum
`1 + x + ⋯ + x ^ (p - 1)`: immediate from the power rule `foxD_pow` and `foxD_of`. -/
theorem foxD_of_self_pow {X : Type*} [DecidableEq X] {K : Type*} [Ring K] (a : X) (p : ℕ) :
    foxD (K := K) a ((FreeGroup.of a) ^ p) =
      ∑ i ∈ Finset.range p, ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of a)) ^ i := by
  rw [foxD_pow, foxD_of, if_pos rfl, mul_one]

/-- The Fox derivative of a power of a letter different from the differentiating letter vanishes:
`∂(y ^ q)/∂x = 0` for `y ≠ x`. -/
theorem foxD_of_ne_pow {X : Type*} [DecidableEq X] {K : Type*} [Ring K] {a b : X}
    (h : b ≠ a) (q : ℕ) :
    foxD (K := K) a ((FreeGroup.of b) ^ q) = 0 := by
  rw [foxD_pow, foxD_of, if_neg h, mul_zero]

/-- **The Fox derivative of a torus word `x ^ p * y ^ q`.**  For `y ≠ x`, the derivative with
respect to `x` is the geometric sum `1 + x + ⋯ + x ^ (p - 1)`: the `y ^ q` factor contributes
nothing, since its derivative vanishes. -/
theorem foxD_letterPow_mul_letterPow {X : Type*} [DecidableEq X] {K : Type*} [Ring K]
    {a b : X} (h : b ≠ a) (p q : ℕ) :
    foxD (K := K) a ((FreeGroup.of a) ^ p * (FreeGroup.of b) ^ q) =
      ∑ i ∈ Finset.range p, ((MonoidAlgebra.of K (FreeGroup X)) (FreeGroup.of a)) ^ i := by
  rw [foxD_mul, foxD_of_self_pow, foxD_of_ne_pow h q, mul_zero, add_zero]

/-- **The component of the root Fox vector of a torus relator.**  For
`u = x ^ p * y ^ q` and `r = u ^ l`, the `x`-component of the Fox vector of the root `u`, pushed
into `K[⟨x, y | r⟩]`, is `∑_{i < p} x̄ ^ i` with `x̄ = presentRho r x` the class of `x`. -/
theorem rootVec_letterPow_mul_letterPow {K : Type*} [Field K] (p q l : ℕ) :
    Work.ORLyndon.rootVec K
      (((FreeGroup.of (0 : Fin 2)) ^ p * (FreeGroup.of (1 : Fin 2)) ^ q) ^ l)
      ((FreeGroup.of (0 : Fin 2)) ^ p * (FreeGroup.of (1 : Fin 2)) ^ q) (0 : Fin 2) =
      ∑ i ∈ Finset.range p,
        (MonoidAlgebra.of K
          (Work.ORLyndon.OneRelatorGroup
            (((FreeGroup.of (0 : Fin 2)) ^ p * (FreeGroup.of (1 : Fin 2)) ^ q) ^ l))
          (Work.ORLyndon.presentRho
            (((FreeGroup.of (0 : Fin 2)) ^ p * (FreeGroup.of (1 : Fin 2)) ^ q) ^ l)
            (FreeGroup.of (0 : Fin 2)))) ^ i := by
  rw [rootVec_apply, foxD_letterPow_mul_letterPow (K := K) (a := (0 : Fin 2)) (b := 1)
    (by decide) p q, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_pow, presentAlg_of]

end Work.ORLyndon
