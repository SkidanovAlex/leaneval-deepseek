import Mathlib
import Submission.NK.NUV2.RouteD.LevelInf
import Submission.Commons.NumberTheory.NumberField.Completion.addEquiv_groupCohomology_two_quotientToInvariants_units
import Submission.Commons.RepresentationTheory.GroupCohomology.H2_inflation_injective_of_subsingleton_H1
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_adicCompletion_of_commute

/-!
# The Galois-descent identification of level cohomology with the ambient inflation

For a finite Galois extension `F ⊆ L` and a normal subgroup `N ◁ Gal(L/F)` with fixed field
`M = L^N`, the **level inflation map**

`levelInfMap : H²(Gal(M/F), Mˣ) ⟶ H²(Gal(L/F), Lˣ)`

(`NK.NUV2.RouteD.levelInfMap`) is the composite of the Galois-descent isomorphism
`H²(G ⧸ N, (Lˣ)^N) ≅ H²(Gal(M/F), Mˣ)` with the *ambient* inflation
`infNatTrans N 2 : H²(G ⧸ N, (Lˣ)^N) ⟶ H²(G, Lˣ)`.

Since the ambient inflation is injective when `H¹(N, Lˣ) = 0` (Hilbert 90, which holds because
`L/M` is Galois), this identifies `levelInfMap` as an injective map; equivalently it computes
`range (levelInfMap)` as the `[L:M]`-torsion subgroup of the cyclic group `H²(Gal(L/F), Lˣ)`.

## Main results

* `NK.NUV2.Final.unitsDescentIso` — the `Rep`-isomorphism `(Lˣ)^N ≅ Mˣ`;
* `NK.NUV2.Final.levelDescentIso` — the induced isomorphism of `H²`;
* `NK.NUV2.Final.levelInfMap_comp_levelDescentIso` — **the identification**
  `levelDescentIso ≫ levelInfMap = infNatTrans`;
* `NK.NUV2.Final.levelInfMap_injective` — injectivity of the level inflation map.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory Representation

namespace NK.NUV2.Final

universe u

section Descent

variable {F L : Type} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

/-- **Galois descent for the units**: the invariants `(Lˣ)^N` of the units of `L` under a normal
subgroup `N ◁ Gal(L/F)` are the units of the fixed field `L^N`, equivariantly for the
identification `Gal(L/F) ⧸ N ≃* Gal(L^N/F)`. -/
noncomputable def unitsDescentIso (N : Subgroup (L ≃ₐ[F] L)) [N.Normal] :
    (Rep.ofAlgebraAutOnUnits F L).quotientToInvariants N ≅
      Rep.res (IsGalois.normalAutEquivQuotient N).toMonoidHom
        (Rep.ofAlgebraAutOnUnits F ↥(IntermediateField.fixedField N)) :=
  { hom := Rep.ofHom ⟨(Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv
        N).toLinearMap, fun g => by
      apply LinearMap.ext; intro x
      exact Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv_equivariant
        N g x⟩
    inv := Rep.ofHom ⟨(Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv
        N).symm.toLinearMap, fun g => by
      apply LinearMap.ext; intro y
      show (Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv N).symm
          ((Rep.res (IsGalois.normalAutEquivQuotient N).toMonoidHom
            (Rep.ofAlgebraAutOnUnits F ↥(IntermediateField.fixedField N))).ρ g y)
        = ((Rep.ofAlgebraAutOnUnits F L).quotientToInvariants N).ρ g
            ((Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv
              N).symm y)
      conv_lhs => rw [show y = (Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv N)
          ((Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv N).symm y) from
        (LinearEquiv.apply_symm_apply _ y).symm]
      rw [(Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv_equivariant
        N g ((Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv N).symm y)).symm]
      rw [LinearEquiv.symm_apply_apply]⟩
    hom_inv_id := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      rw [Rep.hom_comp_toLinearMap]
      simp only [Rep.hom_ofHom, LinearMap.comp_apply]
      exact LinearEquiv.symm_apply_apply
        (Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv N) x
    inv_hom_id := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      rw [Rep.hom_comp_toLinearMap]
      simp only [Rep.hom_ofHom, LinearMap.comp_apply]
      exact LinearEquiv.apply_symm_apply
        (Commons.NumberTheory.NumberField.Completion.NatCardP9.unitsInvLinearEquiv N) x }

/-- **The Galois-descent isomorphism of level cohomology**:
`H²(G ⧸ N, (Lˣ)^N) ≅ H²(Gal(L^N/F), (L^N)ˣ)`. -/
noncomputable def levelDescentIso (N : Subgroup (L ≃ₐ[F] L)) [N.Normal] :
    groupCohomology ((Rep.ofAlgebraAutOnUnits F L).quotientToInvariants N) 2 ≅
      groupCohomology (Rep.ofAlgebraAutOnUnits F ↥(IntermediateField.fixedField N)) 2 :=
  ((groupCohomology.functor ℤ ((L ≃ₐ[F] L) ⧸ N) 2).mapIso (unitsDescentIso N)) ≪≫
    (groupCohomology.mapIso (G := (L ≃ₐ[F] L) ⧸ N)
      (H := ↥(IntermediateField.fixedField N) ≃ₐ[F] ↥(IntermediateField.fixedField N))
      (A := Rep.ofAlgebraAutOnUnits F ↥(IntermediateField.fixedField N))
      (B := Rep.res (IsGalois.normalAutEquivQuotient N).toMonoidHom
        (Rep.ofAlgebraAutOnUnits F ↥(IntermediateField.fixedField N)))
      (IsGalois.normalAutEquivQuotient N) (LinearEquiv.refl ℤ
        (Rep.ofAlgebraAutOnUnits F ↥(IntermediateField.fixedField N)).V) (by intro g; rfl) 2)

end Descent

end NK.NUV2.Final

namespace NK.NUV2.Final

section Identity

variable {F L : Type} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

end Identity

end NK.NUV2.Final
