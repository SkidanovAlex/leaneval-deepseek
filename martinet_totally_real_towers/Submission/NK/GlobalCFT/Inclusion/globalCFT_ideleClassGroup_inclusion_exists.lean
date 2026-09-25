import Mathlib
import Submission.NK.GlobalCFT.Inclusion
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_principalIdele
import Submission.NK.GlobalCFT.IdeleClassGroup

/-!
# The inclusion of idèle class groups

For `L / K` a finite extension of number fields and a monoid homomorphism `φ : 𝕀 K →* 𝕀 L` whose
`w`-component is the local embedding `K_{u w}ˣ →* L_wˣ`, the induced map on idèle class groups
`C_K →* C_L` exists: `φ` carries principal idèles to principal idèles
(`NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_principalIdele`), so it descends to the
quotients of the idèle groups by the principal idèles.

## Main result

* `NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct NumberField.LiesOver
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Inclusion

/-- The principal idèles of `K` are killed by the composite `𝕀 K → 𝕀 L → C L` when `φ` is the
inclusion of idèles induced by the local embeddings of a finite extension `L / K`. -/
theorem globalCFT_principalSubgroup_le_ker_inclusionMk {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (u : Place L → Place K) (hu : ∀ w : Place L, Place.LiesOver w (u w))
    (φ : 𝕀[K] →* 𝕀[L])
    (hφ : ∀ (x : 𝕀[K]) (w : Place L),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w))) :
    Idele.principalSubgroup K ≤ ((IdeleClassGroup.mk L).comp φ).ker := by
  rintro y ⟨z, rfl⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
    globalCFT_ideleInclusion_principalIdele u hu φ hφ z]
  exact (QuotientGroup.eq_one_iff
    (Idele.principalIdele L (Units.map (algebraMap K L).toMonoidHom z))).mpr ⟨_, rfl⟩

/-- **The induced map on idèle class groups.**  A monoid homomorphism `𝕀 K →* 𝕀 L` whose
components are the local embeddings of a finite extension `L / K` descends to the idèle class
groups: the principal idèles are carried to principal idèles. -/
theorem globalCFT_ideleClassGroup_inclusion_exists {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (u : Place L → Place K) (hu : ∀ w : Place L, Place.LiesOver w (u w))
    (φ : 𝕀[K] →* 𝕀[L])
    (hφ : ∀ (x : 𝕀[K]) (w : Place L),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w))) :
    ∃ ψ : C[K] →* C[L], ∀ x : 𝕀[K],
      ψ (IdeleClassGroup.mk K x) = IdeleClassGroup.mk L (φ x) := by
  refine ⟨QuotientGroup.lift (Idele.principalSubgroup K)
    ((IdeleClassGroup.mk L).comp φ)
    (globalCFT_principalSubgroup_le_ker_inclusionMk u hu φ hφ), ?_⟩
  intro x
  exact QuotientGroup.lift_mk' _ _ x

end NK.GlobalCFT.Inclusion
