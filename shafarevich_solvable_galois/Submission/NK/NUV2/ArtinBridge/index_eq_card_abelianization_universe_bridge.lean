import Mathlib
import Submission.NK.GlobalCFTdeep.hasseNorm_index_eq_universe
import Submission.NK.GlobalCFTdeep.normClassSubgroup_index_eq_of_ringEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The universe bridge for `[C_K : N_{L/K} C_L] = |Gal(L/K)^{ab}|`

The statement `[C_K : N_{L/K} C_L] = |Gal(L/K)^{ab}|` for finite Galois extensions `L/K` of number
fields is available in the workspace at universe zero (the type of number fields is `Type`, i.e.
`Type 0`, in the arithmetic developments).  This file removes that restriction: it derives the
statement for number fields in *arbitrary* universes from the universe-zero statement `h0`, with no
new arithmetic.

The argument is pure transport, and is the same one used in
`NK.GlobalCFTdeep.hasseNorm_index_eq_universe` for the *degree* form of Hasse's norm theorem:

* A number field is countable (`Finsupp.Countable.of_moduleFinite`, from `NumberField K` giving
  `Module.Finite ℚ K`), hence `Small.{0}`, hence equivalent to its `Type 0` model
  `Shrink.{0} K` (`Shrink.ringEquiv`).
* On the `Shrink` models, `h0` gives the identity.  Mathlib transports the field and number-field
  structures, and `Submission.NK.GlobalCFTdeep.HasseIndex` transports the extension itself: the
  `Shrink K`-algebra structure on `Shrink L` (`shrinkAlgebra`), finite-dimensionality
  (`shrink_finiteDimensional`), the Galois property (`shrink_isGalois`).
* The norm index is invariant under a ring equivalence of the extensions
  (`NK.GlobalCFTdeep.normClassSubgroup_index_eq_of_ringEquiv`), so it does not change under
  shrinking.
* The order of the abelianisation is an isomorphism invariant of the Galois group, and the Galois
  groups of the extension and of its shrunk model are isomorphic by conjugation with the `Shrink`
  ring equivalence: `Submission.NeukirchUchida.conjHomEquiv` applied to
  `HasseIndex.shrink_mapsBase`, followed by `NK.LocalAnabelian.abelianizationMulEquiv` and
  `Nat.card_congr`.
-/

namespace NK.NUV2.ArtinBridge

set_option linter.style.haveILetI false

theorem index_eq_card_abelianization_universe_bridge
    (h0 : ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L],
      (NK.GlobalCFT.Idele.normClassSubgroup K L).index = Nat.card (Abelianization (L ≃ₐ[K] L)))
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    (NK.GlobalCFT.Idele.normClassSubgroup K L).index = Nat.card (Abelianization (L ≃ₐ[K] L)) := by
  -- A number field is countable, so it has a model in `Type 0`.
  haveI hcK : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := K)
  haveI hcL : Countable L := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := L)
  haveI hsK : Small.{0} K := Countable.toSmall K
  haveI hsL : Small.{0} L := Countable.toSmall L
  -- The universe-zero statement, at the `Shrink` models.
  have h1 := h0 (K := Shrink.{0} K) (L := Shrink.{0} L)
  -- Invariance of the norm index under the ring equivalences of the extensions.
  have h2 := NK.GlobalCFTdeep.normClassSubgroup_index_eq_of_ringEquiv (K := K) (L := L)
    (K' := Shrink.{0} K) (L' := Shrink.{0} L) ((Shrink.ringEquiv K).symm)
    ((Shrink.ringEquiv L).symm)
    (fun x => (NK.GlobalCFTdeep.HasseIndex.shrink_algebraMap_compat_apply K L x).symm)
  -- The Galois groups of the two extensions are isomorphic, hence so are their abelianisations.
  have h3 : Nat.card (Abelianization (L ≃ₐ[K] L))
      = Nat.card (Abelianization (Shrink.{0} L ≃ₐ[Shrink.{0} K] Shrink.{0} L)) :=
    Nat.card_congr (NK.LocalAnabelian.abelianizationMulEquiv
      (Submission.NeukirchUchida.conjHomEquiv
        (NK.GlobalCFTdeep.HasseIndex.shrink_mapsBase K L))).toEquiv.symm
  rw [h2, h1, h3]

end NK.NUV2.ArtinBridge
