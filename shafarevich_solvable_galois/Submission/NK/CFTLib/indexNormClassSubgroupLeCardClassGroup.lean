import Mathlib
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_idealClassMap_exists
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The index of the norm class subgroup is at most the class number

For a finite extension `K ⊆ L` of number fields, the idèle class group `C_K` surjects onto the
ideal class group `Cl(K)` with kernel `I`, the image of the idèles that are local units at every
finite place (`NK.GlobalCFT.Idele.integralIdeles`).  Hence `[C_K : I] = #Cl(K)`.

If moreover `I ≤ N_{L/K} C_L`, then `N_{L/K} C_L` is an intermediate subgroup between `I` and
`C_K`, so `[C_K : N_{L/K} C_L] ≤ [C_K : I] = #Cl(K)`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace NK.CFTLib

open NK.GlobalCFT

theorem indexNormClassSubgroupLeCardClassGroup
    {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (h : (NK.GlobalCFT.Idele.integralIdeles K).map (NK.GlobalCFT.IdeleClassGroup.mk K) ≤
      NK.GlobalCFT.Idele.normClassSubgroup K L) :
    (NK.GlobalCFT.Idele.normClassSubgroup K L).index ≤
      Nat.card (ClassGroup (NumberField.RingOfIntegers K)) := by
  -- The integral idèles are the kernel of the ideal class map on `C_K`.
  have hker : (IdeleClassGroup.idealClassHom K).ker =
      (Idele.integralIdeles K).map (IdeleClassGroup.mk K) := IdeleClassGroup.ker_idealClassHom K
  have hsurj := IdeleClassGroup.idealClassHom_surjective K
  have hrange : (IdeleClassGroup.idealClassHom K).range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
  -- `I = ker (idealClassHom K)` has finite index, since the class group is finite.
  haveI : Finite (IdeleClassGroup.idealClassHom K).range := by rw [hrange]; infer_instance
  haveI : ((Idele.integralIdeles K).map (IdeleClassGroup.mk K)).FiniteIndex := by
    rw [← hker]
    exact Subgroup.finiteIndex_ker (IdeleClassGroup.idealClassHom K)
  -- `[C_K : I] = #Cl(K)`: the index of the kernel of a surjective map is the cardinality of the
  -- target.
  have hIindex : ((Idele.integralIdeles K).map (IdeleClassGroup.mk K)).index =
      Nat.card (ClassGroup (NumberField.RingOfIntegers K)) := by
    rw [← hker, Subgroup.index_ker, hrange, Subgroup.card_top]
  -- The index is antitone in the subgroup.
  calc (Idele.normClassSubgroup K L).index
      ≤ ((Idele.integralIdeles K).map (IdeleClassGroup.mk K)).index := Subgroup.index_antitone h
    _ = Nat.card (ClassGroup (NumberField.RingOfIntegers K)) := hIindex

end NK.CFTLib
