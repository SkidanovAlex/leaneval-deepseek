import Mathlib
import Submission.Work.SSGRoute.CFTSide.classField_exists_of_index
import Submission.Work.SSGRoute.Sha2Lib.mem_normClassSubgroup_iff_of_algEquiv
import Submission.NK.CFTLib.fundamentalClassElement
import Submission.NK.CFTLib.ArtinReciprocityIdealProved
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.GlobalCFT.IdeleClassGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The class field, inside `Ω`, of an open finite-index subgroup of `C_↥K`

`Work.SSGRoute.EscapeCoreLib.exists_intermediateField_normClassSubgroup_eq` produces, for an open
finite-index subgroup `U ≤ C_↥K`, an intermediate field `M : IntermediateField ↥K Ω` with
`N_{M/↥K} C_M = U` and `[M : ↥K] = U.index` (Galois over `↥K`).

The abstract class field is produced by `CFTSide.classField_exists_of_index`; it is transported into
the ambient algebraic closure `Ω` by `IsAlgClosed.lift` and `AlgHom.fieldRange`, and the norm class
subgroup is transported along the resulting `↥K`-algebra equivalence by
`Sha2Lib.mem_normClassSubgroup_iff_of_algEquiv`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField
open NK.GlobalCFT

namespace Work.SSGRoute.EscapeCoreLib

noncomputable section

/-- **The class field, inside `Ω`, of an open finite-index subgroup of `C_↥K`.** -/
theorem exists_intermediateField_normClassSubgroup_eq
    {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (U : Subgroup (IdeleClassGroup ↥K)) (hUfin : U.FiniteIndex)
    (hUopen : IsOpen (U : Set (IdeleClassGroup ↥K))) :
    ∃ (M : IntermediateField ↥K Ω) (_ : FiniteDimensional ↥K M) (_ : IsGalois ↥K M)
      (_ : NumberField ↥M),
      Module.finrank ↥K ↥M = U.index ∧ Idele.normClassSubgroup ↥K ↥M = U := by
  classical
  haveI : U.FiniteIndex := hUfin
  have hpos : 0 < U.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  obtain ⟨L, hFL, hNL, hAL, hfdL, hgalL, hnormL, hdegL⟩ :=
    Work.SSGRoute.CFTSide.classField_exists_of_index (K := ↥K) U.index hpos U hUfin hUopen rfl
  letI : Field L := hFL
  letI : NumberField L := hNL
  letI : Algebra ↥K L := hAL
  letI : FiniteDimensional ↥K L := hfdL
  letI : IsGalois ↥K L := hgalL
  haveI : Algebra.IsAlgebraic ↥K L := Algebra.IsAlgebraic.of_finite ↥K L
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  let ι : L →ₐ[↥K] Ω := IsAlgClosed.lift
  let M : IntermediateField ↥K Ω := ι.fieldRange
  let φ : L ≃ₐ[↥K] ↥M := ι.equivFieldRange
  haveI hfdM : FiniteDimensional ↥K ↥M :=
    FiniteDimensional.of_injective φ.symm.toLinearEquiv.toLinearMap φ.symm.injective
  haveI hgalM : IsGalois ↥K ↥M := IsGalois.of_algEquiv φ
  haveI hnfM : NumberField ↥M := NumberField.of_module_finite ↥K ↥M
  refine ⟨M, hfdM, hgalM, hnfM, ?_, ?_⟩
  · rw [← hdegL, LinearEquiv.finrank_eq φ.toLinearEquiv]
  · rw [show Idele.normClassSubgroup ↥K ↥M = Idele.normClassSubgroup ↥K L from
      SetLike.ext fun x => Work.SSGRoute.Sha2Lib.mem_normClassSubgroup_iff_of_algEquiv φ.symm x,
      hnormL]

end

end Work.SSGRoute.EscapeCoreLib
