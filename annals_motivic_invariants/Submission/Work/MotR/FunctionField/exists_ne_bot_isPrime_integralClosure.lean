import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The integral closure has a nonzero prime ideal

If `A` is a domain embedding into a commutative ring `K` (via an injective `algebraMap A K`) and
`A` has a nonzero prime ideal `p`, then the integral closure `B = integralClosure A K` of `A` in
`K` has a nonzero prime ideal `q`.

This is the lying-over theorem for the integral extension `A ⊆ B`: any prime of the base lifts to a
prime of `B`. Concretely, `Algebra.IsIntegral A B` holds since every element of the integral
closure is integral over `A` by definition, so
`Ideal.exists_ideal_over_prime_of_isIntegral` applied with `I = ⊥` produces a prime `q` of `B` with
`Ideal.under A q = p`. Since `A → B` is injective (its composite with `B → K` is `algebraMap A K`),
the contraction of `⊥` is `⊥`, so `q ≠ ⊥` because `p ≠ ⊥`.
-/

set_option linter.style.haveILetI false

namespace Work.MotR.FunctionField

theorem exists_ne_bot_isPrime_integralClosure {A K : Type} [CommRing A] [IsDomain A] [CommRing K]
    [Algebra A K] (hinj : Function.Injective (algebraMap A K))
    (hA : ∃ p : Ideal A, p ≠ ⊥ ∧ p.IsPrime) :
    ∃ q : Ideal ↥(integralClosure A K), q ≠ ⊥ ∧ q.IsPrime := by
  classical
  obtain ⟨p, hp_ne, hp_prime⟩ := hA
  haveI := hp_prime
  -- The algebra map `A → B` is injective: it agrees with `algebraMap A K` after `B → K`.
  have hInj : Function.Injective (algebraMap A ↥(integralClosure A K)) := by
    intro x y hxy
    apply hinj
    rw [IsScalarTower.algebraMap_apply A ↥(integralClosure A K) K x,
      IsScalarTower.algebraMap_apply A ↥(integralClosure A K) K y, hxy]
  -- Lying over for the integral extension `A ⊆ B`, applied to the ideal `⊥` of `B`.
  have hbot : Ideal.under A (⊥ : Ideal ↥(integralClosure A K)) ≤ p := by
    rw [Ideal.under_def, Ideal.comap_bot_of_injective (algebraMap A ↥(integralClosure A K)) hInj]
    exact bot_le
  obtain ⟨q, -, hq_prime, hq_under⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := A) (S := ↥(integralClosure A K)) p ⊥ hbot
  -- `q ≠ ⊥` since its contraction to `A` is `p ≠ ⊥` and `⊥` contracts to `⊥`.
  exact ⟨q, fun hq => hp_ne (by rw [← hq_under, hq, Ideal.under_def,
    Ideal.comap_bot_of_injective (algebraMap A ↥(integralClosure A K)) hInj]), hq_prime⟩

end Work.MotR.FunctionField
