import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cardinality of `𝒪 / 𝔪 ^ n` for the integers of an adic completion

For a number field `K` and a finite place `𝔭`, the ring of integers
`𝒪 = 𝔭.adicCompletionIntegers K` of the completion is a discrete valuation ring, hence a
Dedekind domain.  Its maximal ideal `𝔪` is the unique non-zero prime, and in a Dedekind
domain the quotient `R ⧸ P ^ n` by a power of a prime ideal `P ≠ ⊥` has cardinality
`|R ⧸ P| ^ n` (`cardQuot_pow_of_prime`).  Since `IsLocalRing.ResidueField R = R ⧸ 𝔪` by
definition, this is exactly the statement below.
-/

namespace NK.LocalInputs.PowerQuotient

/-- The quotient of the integers of the `𝔭`-adic completion by the `n`-th power of its maximal
ideal has cardinality the `n`-th power of the cardinality of the residue field. -/
theorem natCard_quot_maximalIdeal_pow {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ) :
    Nat.card ((𝔭.adicCompletionIntegers K) ⧸
        (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)) ^ n) =
      (Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))) ^ n := by
  -- `IsLocalRing.ResidueField R` and `R ⧸ maximalIdeal R` are the same type, and
  -- `Nat.card (M ⧸ S) = Submodule.cardQuot S` holds by definition (`rfl`).
  rw [show Nat.card ((𝔭.adicCompletionIntegers K) ⧸
        (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)) ^ n)
      = Submodule.cardQuot ((IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)) ^ n)
      from rfl]
  rw [show Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K))
      = Submodule.cardQuot (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K))
      from rfl]
  -- The integers of the completion form a discrete valuation ring, hence a Dedekind domain,
  -- and its maximal ideal is prime (indeed maximal) and non-zero.
  exact cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field _)

end NK.LocalInputs.PowerQuotient
