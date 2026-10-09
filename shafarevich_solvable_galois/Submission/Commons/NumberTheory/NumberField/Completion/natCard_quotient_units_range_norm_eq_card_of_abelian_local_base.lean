import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_card_of_abelian_pgroup_base
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum

namespace Commons.NumberTheory.NumberField.Completion

set_option linter.style.haveILetI false

/-- Abelian local norm index result, general base field: for a finite-dimensional extension `B`
of a `p`-adic local field `F = Q.adicCompletion K` (`K` a number field, `Q` a finite place) and a
finite abelian Galois extension `E / B` with commutative Galois group, the index of the norm group
`N_{E/B}(Eˣ)` in `Bˣ` equals the order of `Gal(E/B)`.

This is the general abelian case of the local norm index theorem, and it is the special case
`p = 0` of the `p`-group statement `natCard_quotient_units_range_norm_eq_card_of_abelian_pgroup_base`:
for `p = 0` the hypothesis `IsPGroup 0 G` is satisfied by every group `G` (`IsPGroup.zero`), so the
`p`-group theorem applied with `p = 0` *is* the abelian theorem.  Concretely,
`natCard_quotient_units_range_norm_eq_card_of_abelian_pgroup_base` is proved from the deep lower
bound `natCard_quotient_units_range_norm_pgroup_intermediate_field` (the fundamental class / Tate's
theorem route, i.e. local class field theory) via the elementary upper bound
`natCard_quotient_units_range_norm_le_card_of_abelian_local_base`.

The shared commons also reduces this statement to the prime-power case
(`natCard_quotient_units_range_norm_eq_card_of_abelian_of_prime_power`), so it suffices to treat
`Gal(E/B)` a `p`-group; then `E/B` is totally wildly ramified, and via
`abelian_local_norm_index_of_prime_top_kernel_condition` it suffices to prove the tower kernel
condition `ker N_{B₁/B} ≤ range N_{E/B₁}` for towers with `E/B₁` of prime degree. Related results
already in the commons: `kernel_condition_of_unramified_top`,
`kernel_condition_of_prime_top_cyclic_middle_coprime`, the cyclic case at an arbitrary base
(`natCard_quotient_units_range_norm_eq_card_of_cyclic_arbitrary_base'`), the existence of a stable
open subgroup of the units with vanishing low-degree Tate cohomology
(`exists_open_subgroup_units_cohomology_trivial`), and Hilbert 90 (Mathlib,
`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`). -/
theorem natCard_quotient_units_range_norm_eq_card_of_abelian_local_base
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
  natCard_quotient_units_range_norm_eq_card_of_abelian_pgroup_base
    (K := K) Q hcomm (p := 0) (IsPGroup.zero (E ≃ₐ[B] E))

end Commons.NumberTheory.NumberField.Completion
