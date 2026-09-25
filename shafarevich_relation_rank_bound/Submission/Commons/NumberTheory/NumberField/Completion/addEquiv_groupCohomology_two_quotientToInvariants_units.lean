import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_groupCohomology_two_units_le_finrank_of_abelian
import Submission.Commons.RepresentationTheory.GroupCohomology.natCard_groupCohomology_res_mulEquiv

open CategoryTheory Representation

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Commons.NumberTheory.NumberField.Completion

theorem addEquiv_groupCohomology_two_quotientToInvariants_units
    {B E : Type} [Field B] [Field E] [Algebra B E] [FiniteDimensional B E] [IsGalois B E]
    (H : Subgroup (E ≃ₐ[B] E)) [H.Normal] :
    Nonempty (groupCohomology ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H) 2 ≃+
      groupCohomology (Rep.ofAlgebraAutOnUnits B ↥(IntermediateField.fixedField H)) 2) := by
  haveI : Normal B ↥(IntermediateField.fixedField H) := by
    haveI : IsGalois B ↥(IntermediateField.fixedField H) := IsGalois.of_fixedField_normal_subgroup H
    infer_instance
  have hiso : (Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H ≅
      Rep.res (IsGalois.normalAutEquivQuotient H).toMonoidHom
        (Rep.ofAlgebraAutOnUnits B ↥(IntermediateField.fixedField H)) :=
    { hom := Rep.ofHom ⟨(NatCardP9.unitsInvLinearEquiv H).toLinearMap, fun g => by
        apply LinearMap.ext; intro x
        exact NatCardP9.unitsInvLinearEquiv_equivariant H g x⟩
      inv := Rep.ofHom ⟨(NatCardP9.unitsInvLinearEquiv H).symm.toLinearMap, fun g => by
        apply LinearMap.ext; intro y
        show (NatCardP9.unitsInvLinearEquiv H).symm
            ((Rep.res (IsGalois.normalAutEquivQuotient H).toMonoidHom
              (Rep.ofAlgebraAutOnUnits B ↥(IntermediateField.fixedField H))).ρ g y)
          = ((Rep.ofAlgebraAutOnUnits B E).quotientToInvariants H).ρ g
              ((NatCardP9.unitsInvLinearEquiv H).symm y)
        conv_lhs => rw [show y = (NatCardP9.unitsInvLinearEquiv H) ((NatCardP9.unitsInvLinearEquiv H).symm y) from
          (LinearEquiv.apply_symm_apply (NatCardP9.unitsInvLinearEquiv H) y).symm]
        rw [(NatCardP9.unitsInvLinearEquiv_equivariant H g ((NatCardP9.unitsInvLinearEquiv H).symm y)).symm]
        rw [LinearEquiv.symm_apply_apply]⟩
      hom_inv_id := by
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        rw [Rep.hom_comp_toLinearMap]
        simp only [Rep.hom_ofHom, LinearMap.comp_apply]
        exact LinearEquiv.symm_apply_apply (NatCardP9.unitsInvLinearEquiv H) x
      inv_hom_id := by
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        rw [Rep.hom_comp_toLinearMap]
        simp only [Rep.hom_ofHom, LinearMap.comp_apply]
        exact LinearEquiv.apply_symm_apply (NatCardP9.unitsInvLinearEquiv H) x }
  refine ⟨(Iso.toLinearEquiv ((groupCohomology.functor ℤ ((E ≃ₐ[B] E) ⧸ H) 2).mapIso hiso)).toAddEquiv.trans ?_⟩
  exact (Iso.toLinearEquiv (groupCohomology.mapIso (G := (E ≃ₐ[B] E) ⧸ H)
      (H := ↥(IntermediateField.fixedField H) ≃ₐ[B] ↥(IntermediateField.fixedField H))
      (A := Rep.ofAlgebraAutOnUnits B ↥(IntermediateField.fixedField H))
      (B := Rep.res (IsGalois.normalAutEquivQuotient H).toMonoidHom
        (Rep.ofAlgebraAutOnUnits B ↥(IntermediateField.fixedField H)))
      (IsGalois.normalAutEquivQuotient H)
      (LinearEquiv.refl ℤ (Rep.ofAlgebraAutOnUnits B
        ↥(IntermediateField.fixedField H)).V) (by intro g; rfl) 2)).toAddEquiv

end Commons.NumberTheory.NumberField.Completion
