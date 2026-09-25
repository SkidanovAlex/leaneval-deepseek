import Mathlib
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.GlobalCFTdeep.Transport.NormGroupTransport
import Submission.NK.Reconstruct.normal_restrictLevelTo

set_option linter.style.haveILetI false

namespace NK.NUV2.ArtinBridge

/-- **Monotonicity of the norm subgroup of the idèle class group along intermediate fields.**

If `K ⊆ E ⊆ F ⊆ Ω` are number fields (with `Ω` a field containing `K`), then
`N_{F/K} C_F ≤ N_{E/K} C_E`: the norm subgroup gets smaller as the field grows.  This is the
tower property `NK.GlobalCFT.Idele.normClassSubgroup_le_of_tower` specialised to intermediate
fields of a common extension `Ω`, with the `K`-algebra structure on `↥E` and the `↥E`-algebra
structure on `↥F` obtained from the inclusion `E ≤ F`. -/
theorem normClassSubgroup_le_of_intermediateField_le {K : Type} [Field K] [NumberField K]
    {Ω : Type} [Field Ω] [Algebra K Ω] (E F : IntermediateField K Ω) (h : E ≤ F)
    [FiniteDimensional K E] [NumberField ↥E] [FiniteDimensional K F] [NumberField ↥F] :
    NK.GlobalCFT.Idele.normClassSubgroup K ↥F ≤ NK.GlobalCFT.Idele.normClassSubgroup K ↥E := by
  -- `↥F` is an `↥E`-algebra through the inclusion `E ≤ F`, compatibly with the `K`-structures.
  letI : Algebra ↥E ↥F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower K ↥E ↥F := IsScalarTower.of_algebraMap_eq' rfl
  -- `F` is finite over `E` because it is finite over the smaller field `K`.
  haveI : FiniteDimensional ↥E ↥F := Module.Finite.of_restrictScalars_finite K ↥E ↥F
  exact NK.GlobalCFT.Idele.normClassSubgroup_le_of_tower (K := K) (L := ↥E) (M := ↥F)

end NK.NUV2.ArtinBridge
