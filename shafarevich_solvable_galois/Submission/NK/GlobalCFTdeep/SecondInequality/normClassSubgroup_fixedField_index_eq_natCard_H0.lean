import Mathlib
import Submission.NK.GlobalCFTdeep.AbstractH0
import Submission.NK.GlobalCFT.GlobalCFT
import Submission.NK.GlobalCFT.H0Computation
import Submission.NK.GlobalCFTdeep.SecondInequality.normClassSubgroup_index_eq_natCard_H0
import Submission.NK.GlobalCFTdeep.SecondInequality.natCard_H0_eq_of_mulEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace NK.GlobalCFTdeep.SecondInequality

/-- The `H⁰`-computation for the sub-extension `L / L^S`: for a finite Galois extension `L / K` of number fields and a subgroup `S ≤ Gal(L/K)`, the index of the norm class subgroup of the extension `L / L^S` equals `Nat.card (H0 ↥S (C_L))`, where `↥S` acts on `C_L` through the given `Gal(L/K)`-action (i.e. the instance `Subgroup.instMulDistribMulAction`).

Proof plan.  Apply `NK.GlobalCFTdeep.SecondInequality.normClassSubgroup_index_eq_natCard_H0` to the Galois extension `L / ↥(IntermediateField.fixedField S)` (instances: `NumberField ↥(IntermediateField.fixedField S)`, `FiniteDimensional ↥(IntermediateField.fixedField S) L`, `IsGalois ↥(IntermediateField.fixedField S) L`, all available by `inferInstance` as in `NK.GlobalCFTdeep.subsingleton_groupCohomology_one_res_ideleClassGroup_of_isPGroup`).  This gives the left side as `Nat.card (H0 (L ≃ₐ[↥(fixedField S)] L) (C_L))`, and the group isomorphism `IntermediateField.subgroupEquivAlgEquiv S : ↥S ≃* (L ≃ₐ[↥(fixedField S)] L)` transports it to `Nat.card (H0 ↥S (C_L))` by `NK.GlobalCFTdeep.natCard_H0_eq_of_mulEquiv`, whose compatibility hypothesis holds by `rfl`/`intro g m; rfl` (the two actions agree because both apply the same automorphism of `L` to `C_L`; the same `rfl` appears in `NK.GlobalCFTdeep.subsingleton_groupCohomology_one_res_ideleClassGroup_of_isPGroup` as the `(by intro g; rfl)` argument of `groupCohomology.mapIso`).  Note the fields live in `Type` (universe `0`) throughout, as in `normClassSubgroup_index_eq_natCard_H0`. -/
theorem normClassSubgroup_fixedField_index_eq_natCard_H0 {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Subgroup (L ≃ₐ[K] L)) [Fintype ↥S] :
    (NK.GlobalCFT.Idele.normClassSubgroup ↥(IntermediateField.fixedField S) L).index =
      Nat.card (NK.GlobalCFTdeep.H0 ↥S (NK.GlobalCFT.IdeleClassGroup L)) := by
  classical
  let K' : IntermediateField K L := IntermediateField.fixedField S
  haveI : NumberField ↥K' := inferInstance
  haveI : FiniteDimensional ↥K' L := inferInstance
  haveI : IsGalois ↥K' L := inferInstance
  have h1 := normClassSubgroup_index_eq_natCard_H0 (K := ↥K') (L := L)
  have h2 := natCard_H0_eq_of_mulEquiv (G := ↥S) (G' := (L ≃ₐ[↥K'] L))
      (M := NK.GlobalCFT.IdeleClassGroup L)
      (IntermediateField.subgroupEquivAlgEquiv S) (by intro g m; rfl)
  exact h1.trans h2.symm

end NK.GlobalCFTdeep.SecondInequality
