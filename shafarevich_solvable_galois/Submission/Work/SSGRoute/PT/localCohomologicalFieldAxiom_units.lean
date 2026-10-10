import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Submission.Work.SSGRoute.eb_loc_card
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local cohomological field axiom for the units of a `p`-adic level

`Work.SSGRoute.PT.localCohomologicalFieldAxiom_units`: for `K` a number field, `Q` a finite place of
`K`, `F` a finite extension of the `Q`-adic completion `K_Q` and `E / F` a finite Galois extension,

* `H¹(H, Eˣ) = 0` for every subgroup `H ≤ Gal(E/F)` (Hilbert 90);
* `#H²(H, Eˣ) = #H` for every subgroup `H ≤ Gal(E/F)`;
* `H²(Gal(E/F), Eˣ)` contains an element of order `#Gal(E/F)` (the local fundamental class).

This is the local analogue of `NK.GlobalCFT.CohomologicalFieldAxiom` for the units of a `p`-adic
level, and is the input consumed by
`Commons.RepresentationTheory.TateCohomology.natCard_tateCohomology_eq_of_fundamental_class`.

The three components are assembled from on-disk local class field theory:

1. `Commons.NumberTheory.NumberField.Completion.subsingleton_groupCohomology_one_res_units`
   is Hilbert 90 for an arbitrary subgroup, transported to the fixed field;
2. `Commons.NumberTheory.NumberField.Completion.NatCardP9.natCard_groupCohomology_two_res_units`
   identifies `H²(H, Eˣ)` with `H²(Gal(E/E^H), Eˣ)`, to which the on-disk invariant-map /
   Brauer-group statement `NK.NUV2.LC.natCard_groupCohomology_two_units_local_eq_finrank`
   applies: `#H²(Gal(E/E^H), Eˣ) = [E : E^H] = #H`
   (`IntermediateField.finrank_fixedField_eq_card`);
3. `NK.NUV2.LC.exists_addOrderOf_eq_finrank_groupCohomology_two_units_local` gives an element of
   order `[E : F] = #Gal(E/F)` (`IsGalois.card_aut_eq_finrank`).
-/

set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.SSGRoute.PT

open CategoryTheory Representation

theorem localCohomologicalFieldAxiom_units {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {F E : Type} [Field F] [Field E] [Algebra (Q.adicCompletion K) F] [Algebra F E]
    [Algebra (Q.adicCompletion K) E] [IsScalarTower (Q.adicCompletion K) F E]
    [FiniteDimensional (Q.adicCompletion K) F] [FiniteDimensional F E]
    [FiniteDimensional (Q.adicCompletion K) E] [IsGalois F E] :
    (∀ H : Subgroup (E ≃ₐ[F] E),
        Subsingleton (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits F E)) 1)) ∧
      (∀ H : Subgroup (E ≃ₐ[F] E),
        Nat.card (groupCohomology (Rep.res H.subtype (Rep.ofAlgebraAutOnUnits F E)) 2)
          = Nat.card H) ∧
      (∃ α : groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2,
        addOrderOf α = Nat.card (E ≃ₐ[F] E)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- ## Hilbert 90, at every subgroup
    intro H
    exact Commons.NumberTheory.NumberField.Completion.subsingleton_groupCohomology_one_res_units H
  · -- ## `#H²(H, Eˣ) = #H`, by the invariant map at the fixed field `E^H`
    intro H
    -- transport the coefficient ring from `F` to the fixed field `E^H`, where the acting group is
    -- `H` itself (definitionally the same representation on `Eˣ`, with the same action)
    rw [Commons.NumberTheory.NumberField.Completion.NatCardP9.natCard_groupCohomology_two_res_units H]
    let C : IntermediateField F E := IntermediateField.fixedField H
    -- the `K_Q`-algebra structure on `E^H` induced from `K_Q → F → E^H`, together with the
    -- finiteness and scalar-tower instances that `FiniteDimensional` needs
    letI instAlgC : Algebra (Q.adicCompletion K) ↥C :=
      ((algebraMap F ↥C).comp (algebraMap (Q.adicCompletion K) F)).toAlgebra
    haveI instSTBC : IsScalarTower (Q.adicCompletion K) F ↥C :=
      IsScalarTower.of_algebraMap_eq (fun x => rfl)
    letI instModC : Module (Q.adicCompletion K) ↥C := instAlgC.toModule
    haveI instFdC : Module.Finite (Q.adicCompletion K) ↥C :=
      Module.Finite.trans (R := Q.adicCompletion K) F ↥C
    haveI instFdC' : FiniteDimensional (Q.adicCompletion K) ↥C := instFdC
    haveI instSTCE : IsScalarTower (Q.adicCompletion K) ↥C E :=
      IsScalarTower.of_algebraMap_eq (fun x => by
        rw [IsScalarTower.algebraMap_apply (Q.adicCompletion K) F ↥C x,
          ← IsScalarTower.algebraMap_apply F ↥C E (algebraMap (Q.adicCompletion K) F x),
          ← IsScalarTower.algebraMap_apply (Q.adicCompletion K) F E x])
    -- the Brauer group of the local extension `E / E^H` has order `[E : E^H] = #H`
    rw [NK.NUV2.LC.natCard_groupCohomology_two_units_local_eq_finrank (K := K) Q
          (F := ↥C) (E := E),
      IntermediateField.finrank_fixedField_eq_card H]
  · -- ## the local fundamental class
    obtain ⟨α, hα⟩ :=
      NK.NUV2.LC.exists_addOrderOf_eq_finrank_groupCohomology_two_units_local (K := K) Q
        (F := F) (E := E)
    exact ⟨α, by rw [hα, IsGalois.card_aut_eq_finrank F E]⟩

end Work.SSGRoute.PT
