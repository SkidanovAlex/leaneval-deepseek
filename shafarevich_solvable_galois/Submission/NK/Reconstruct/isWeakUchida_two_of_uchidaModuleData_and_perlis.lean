import Mathlib
import Submission.NK.UchidaKummer.Defs
import Submission.NK.UchidaKummer.Uchida.Abstract
import Submission.NK.UchidaKummer.Uchida.Main
import Submission.NK.UchidaKummer.Uchida.IsomorphicAbsGalois
import Submission.NK.UchidaKummer.Uchida.PerlisInput
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Reconstruct

/-- At `ℓ = 2` the Kummer hypothesis `μ_ℓ ⊆ K` of the weak Neukirch–Uchida theorem is automatic:
every field of characteristic `≠ 2` contains `-1`, a primitive second root of unity. -/
theorem isWeakUchida_two_exists_isPrimitiveRoot (K : Type*) [Field K] [CharZero K] :
    ∃ ζ : K, IsPrimitiveRoot ζ 2 :=
  ⟨-1, IsPrimitiveRoot.neg_one 0 two_ne_zero.symm⟩

/-- **The weak Neukirch–Uchida theorem at `ℓ = 2`, from Uchida's module data and Perlis/Gassmann.**

`IsWeakUchida 2` asks that two number fields with isomorphic absolute Galois groups be isomorphic.
The classical weak theorem `NK.UchidaKummer.nonempty_ringEquiv_of_uchidaModuleData_and_perlis_abs`
supplies this from `IsUchidaModuleData 2` and `PerlisGassmannInput` provided both fields contain
`μ_2`; at `ℓ = 2` that hypothesis is automatic, since `-1` is always a primitive second root of
unity in a field of characteristic `≠ 2` (`isWeakUchida_two_exists_isPrimitiveRoot`). -/
theorem isWeakUchida_two_of_uchidaModuleData_and_perlis (hU : NK.UchidaKummer.IsUchidaModuleData 2) (hP : NK.UchidaKummer.PerlisGassmannInput) : NK.UchidaKummer.IsWeakUchida 2 := by
  intro K₁ K₂ _ _ _ _ K₁' _ _ _ K₂' _ _ _ hiso
  obtain ⟨φ⟩ := hiso
  exact NK.UchidaKummer.nonempty_ringEquiv_of_uchidaModuleData_and_perlis_abs
    hU hP K₁ K₂
    (isWeakUchida_two_exists_isPrimitiveRoot K₁)
    (isWeakUchida_two_exists_isPrimitiveRoot K₂)
    (NK.UchidaKummer.hasIsomorphicAbsGalois_of_galoisEquiv φ)

end NK.Reconstruct
