import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_pgroup_intermediate_field
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Completion

/-- **The abelian local norm index theorem for an arbitrary base field.**

Let `K` be a number field, `Q` a finite place of `K`, so that `F = Q.adicCompletion K` is a
nonarchimedean local field of characteristic `0`.  Let `B / F` be a finite extension field and
`E / B` a finite *abelian* Galois extension.  Then the group of units of `B` modulo the norms
from `E` has the same cardinality as the Galois group `Gal(E/B)`.

This is the norm index theorem of local class field theory.  The proof is the standard chain of
elementary reductions: the norm index is submultiplicative in towers, hence bounded above by
`#Gal(E/B)` (`natCard_quotient_units_range_norm_le_card_of_abelian_local_base`), and the
`ℓ`-primary (Sylow) reduction
(`natCard_quotient_units_range_norm_eq_card_of_abelian_of_prime_power`) reduces the identity for
`E` to the identity for every intermediate field `M` of `E / B` with prime power Galois group
(`natCard_quotient_units_range_norm_pgroup_intermediate_field`). -/
theorem abelian_local_norm_index_at_base
    {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {B E : Type*} [Field B] [Field E]
    [Algebra (Q.adicCompletion K) B] [Algebra B E] [Algebra (Q.adicCompletion K) E]
    [IsScalarTower (Q.adicCompletion K) B E]
    [FiniteDimensional (Q.adicCompletion K) B] [FiniteDimensional B E]
    [IsGalois B E]
    (hcomm : ∀ a b : E ≃ₐ[B] E, a * b = b * a) :
    Nat.card (Bˣ ⧸ MonoidHom.range (Units.map (Algebra.norm B : E →* B))) =
      Nat.card (E ≃ₐ[B] E) :=
  natCard_quotient_units_range_norm_eq_card_of_abelian_of_prime_power (K := K) Q hcomm
    (natCard_quotient_units_range_norm_le_card_of_abelian_local_base (K := K) Q hcomm)
    (natCard_quotient_units_range_norm_pgroup_intermediate_field (K := K) Q hcomm)

end Commons.NumberTheory.NumberField.Completion
