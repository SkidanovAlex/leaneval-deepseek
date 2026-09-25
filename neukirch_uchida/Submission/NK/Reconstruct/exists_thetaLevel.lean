import Mathlib
import Submission.NK.Reconstruct.ambient4f3
import Submission.NK.Reconstruct.conjLevel
import Submission.NK.Reconstruct.PlaceCorrespondence

namespace NK.Reconstruct

set_option linter.style.haveILetI false

open scoped NumberField

/-- **The `θ`-image of a finite Galois level.**  For a finite Galois number-field level `K` of
`Ω/ℚ` and a `ℚ`-algebra automorphism `θ` of `Ω`, the image `θ⁻¹(K)` is again a finite Galois
number-field level of `Ω/ℚ`, and `Ω` is a separable closure of it.

Its underlying field is `K.L.map θ.symm.toAlgHom`.  The analogue of the construction for a base
level `L` already exists in `Submission/Work/Reconstruct/conjLevel.lean` as `conjLevel` /
`conjFrobLevel` (a `FrobLevel ↥L K'`) together with `conjLevelRingEquiv`,
`conjLevelAlgEquivHom` and `conjLevelAlgEquivHom_restrictNormalHom`; the present statement is the
version over the base `ℚ` (so that `M` is a `FrobLevel ℚ Ω`, as `Gamma ↥M.L Ω ℓ` and `ambientPi`
require), and its `IsSepClosure ↥M.L Ω` conjunct follows from `[IsSepClosure ℚ Ω]` via
`isSepClosure_level` / `IsSepClosure.sep_closed`.

The delicate point is an instance diamond: `↥K.L` carries both the `IntermediateField`'s
`Algebra ℚ` structure (`K.L.algebra'`) and the canonical `DivisionRing.toRatAlgebra` one, so the
`FiniteDimensional`/`Normal`/`NumberField` fields have to be stated with the instances the
`FrobLevel` structure actually expects.  `FiniteDimensional` and `NumberField` synthesize via
`IntermediateField.finiteDimensional_map` and
`Commons.NumberTheory.NumberField.numberField_of_intermediateField`; `Normal` follows from
`IntermediateField.equivMap K.L θ.symm.toAlgHom` and `AlgEquiv.transfer_normal` /
`Normal.of_algEquiv`.  Hence the existential packaging. -/
theorem exists_thetaLevel {Ω : Type*} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsSepClosure ℚ Ω]
    (K : NK.Reconstruct.FrobLevel ℚ Ω) (θ : Ω ≃ₐ[ℚ] Ω) :
    ∃ (M : NK.Reconstruct.FrobLevel ℚ Ω), M.L = K.L.map θ.symm.toAlgHom ∧
      IsSepClosure ↥M.L Ω := by
  -- Pin the `Algebra ℚ` structure on both levels to the `IntermediateField` one
  -- (`IntermediateField.algebra'`), so that type class search no longer mixes it up with the
  -- canonical `DivisionRing.toRatAlgebra` structure on a characteristic zero field.
  letI : Algebra ℚ ↥K.L := IntermediateField.algebra' K.L
  letI : Algebra ℚ ↥(K.L.map θ.symm.toAlgHom) :=
    IntermediateField.algebra' (K.L.map θ.symm.toAlgHom)
  refine ⟨{ L := K.L.map θ.symm.toAlgHom,
            finite := ?_,
            normal := ?_,
            numberField := ?_ }, ?_, ?_⟩
  · haveI := K.finite
    exact IntermediateField.finiteDimensional_map θ.symm.toAlgHom
  · haveI : Normal ℚ ↥K.L := K.normal
    exact Normal.of_algEquiv (IntermediateField.equivMap K.L θ.symm.toAlgHom)
  · haveI := K.finite
    exact Commons.NumberTheory.NumberField.numberField_of_intermediateField
      (K.L.map θ.symm.toAlgHom)
  · rfl
  · exact isSepClosure_level (K.L.map θ.symm.toAlgHom)

end NK.Reconstruct
