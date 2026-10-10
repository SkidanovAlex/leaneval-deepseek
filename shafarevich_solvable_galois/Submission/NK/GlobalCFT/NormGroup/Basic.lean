import Mathlib.Basic.Real.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFT.Norm.globalCFT_abs_normIdeleHom
import Submission.NK.GlobalCFT.NormGroup.globalCFT_normClassHom_trans
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm subgroup of the idèle class group

`Idele.normClassSubgroup K L = N_{L/K} C_L` is defined as the image of the norm subgroup of the
idèles `N_{L/K} 𝕀 L` in `C_K`; here we identify it with the range of the norm homomorphism
`IdeleClassGroup.normClassHom K L : C_L →* C_K` (so that membership can be phrased elementwise),
and we record its monotonicity in a tower `K ⊆ L ⊆ M`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT

namespace Idele

variable {K L M : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [NumberField M] [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]

/-- The norm subgroup of the idèles is the range of the idèlic norm. -/
theorem normImage_eq_range : normImage K L = (normIdeleHom K L).range := by
  ext x
  rw [mem_normImage, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, Idele.ext fun v => (hy v).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, fun v => (Idele.normIdeleHom_apply y v).symm⟩

/-- **The norm subgroup as the range of the norm homomorphism**: `N_{L/K} C_L` is exactly the
range of `IdeleClassGroup.normClassHom K L`. -/
theorem normClassSubgroup_eq_range :
    normClassSubgroup K L = (IdeleClassGroup.normClassHom K L).range := by
  ext x
  rw [normClassSubgroup, Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [normImage_eq_range, MonoidHom.mem_range] at hy
    obtain ⟨z, rfl⟩ := hy
    exact ⟨IdeleClassGroup.mk L z, IdeleClassGroup.normClassHom_mk z⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨z, rfl⟩ := IdeleClassGroup.mk_surjective L q
    refine ⟨Idele.normIdeleHom K L z, ?_, ?_⟩
    · rw [normImage_eq_range, MonoidHom.mem_range]
      exact ⟨z, rfl⟩
    · rw [IdeleClassGroup.normClassHom_mk]

/-- Membership in the norm subgroup of the idèle class group. -/
theorem mem_normClassSubgroup {q : IdeleClassGroup K} :
    q ∈ normClassSubgroup K L ↔ ∃ y : IdeleClassGroup L,
      IdeleClassGroup.normClassHom K L y = q := by
  rw [normClassSubgroup_eq_range, MonoidHom.mem_range]

/-- **Monotonicity of the norm subgroups in a tower**: for `K ⊆ L ⊆ M` one has
`N_{M/K} C_M ≤ N_{L/K} C_L`. -/
theorem normClassSubgroup_le_of_tower :
    normClassSubgroup K M ≤ normClassSubgroup K L := by
  intro q hq
  rw [mem_normClassSubgroup] at hq ⊢
  obtain ⟨y, rfl⟩ := hq
  exact ⟨IdeleClassGroup.normClassHom L M y, NormGroup.globalCFT_normClassHom_trans y⟩

/-- **The norm preserves the content** of an idèle class: `|N_{L/K} c|_K = |c|_L`. -/
theorem abs_normClassHom (q : IdeleClassGroup L) :
    IdeleClassGroup.abs K (IdeleClassGroup.normClassHom K L q) =
      IdeleClassGroup.abs L q := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L q
  rw [IdeleClassGroup.normClassHom_mk, IdeleClassGroup.abs_mk, IdeleClassGroup.abs_mk]
  exact Norm.globalCFT_abs_normIdeleHom x

/-- The norm of a norm-one idèle class is again norm-one: `N_{L/K} C¹_L ≤ C¹_K`. -/
theorem normClassHom_mem_ker_abs {q : IdeleClassGroup L}
    (hq : q ∈ (IdeleClassGroup.abs L).ker) :
    IdeleClassGroup.normClassHom K L q ∈ (IdeleClassGroup.abs K).ker := by
  rw [MonoidHom.mem_ker, abs_normClassHom, MonoidHom.mem_ker.mp hq]

end Idele

end NK.GlobalCFT
