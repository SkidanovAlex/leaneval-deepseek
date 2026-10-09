import Mathlib
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_two_eq_tateCohomology_zero_cyclic
import Submission.Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_zero_units
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.RepresentationTheory.GroupCohomology

open CategoryTheory Representation

/-- **Cyclic Neukirch–Uchida input.**  For a finite cyclic Galois extension `L/K` of fields, the
second group cohomology of the units `Lˣ` (with the Galois action) has the cardinality of
`Kˣ ⧸ N_{L/K}(Lˣ)`.

This combines the cyclic periodicity isomorphism `H² ≅ Ĥ⁰` (in cardinality form,
`natCard_groupCohomology_two_eq_tateCohomology_zero_cyclic`) with the computation of the
multiplicative zeroth Tate cohomology as the norm cokernel
(`natCard_tateCohomology_zero_units`). -/
theorem natCard_groupCohomology_two_units_of_cyclic (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) =
      Nat.card (Kˣ ⧸ MonoidHom.range (Units.map (Algebra.norm K : L →* K))) := by
  -- Cyclic periodicity: `H²(Gal(L/K), Lˣ) ≅ Ĥ⁰(Gal(L/K), Lˣ)`, in cardinality form.
  have hper := natCard_groupCohomology_two_eq_tateCohomology_zero_cyclic
    (G := L ≃ₐ[K] L) (V := Additive (Lˣ))
    (ρ := Representation.ofMulDistribMulAction (L ≃ₐ[K] L) (Lˣ))
  -- `Rep.ofAlgebraAutOnUnits K L` is *by definition* the representation of the Galois group
  -- on the units of `L`.
  rw [show Rep.of (Representation.ofMulDistribMulAction (L ≃ₐ[K] L) (Lˣ))
      = Rep.ofAlgebraAutOnUnits K L from rfl] at hper
  rw [hper]
  -- The multiplicative zeroth Tate cohomology of the units is the norm cokernel.
  exact Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_zero_units K L

end Commons.RepresentationTheory.GroupCohomology
