import Submission.NK.GlobalCFTdeep.Transport.IdeleClassEquiv
import Submission.NK.GlobalCFTdeep.Transport.ideleEquiv_normIdeleHom

/-!
# Transport of the norm subgroup and of its index along a ring equivalence

Building on the naturality of the idèlic norm (`ideleEquiv_normIdeleHom`), we show that the idèle
class group transport `ideleClassEquiv eK : C_K ≃* C_{K'}` maps the norm subgroup
`N_{L/K} C_L` onto `N_{L'/K'} C_{L'}`.  Consequently the indices (the "norm indices") agree,
which is the content of the target theorem.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.Transport

open NK.GlobalCFT

variable {K L K' L' : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [Field K'] [NumberField K'] [Field L'] [NumberField L']
  [Algebra K' L'] [FiniteDimensional K' L']

/-- Naturality of the norm homomorphism of idèle class groups for a compatible pair of ring
equivalences: `ideleClassEquiv eK ∘ N_{L/K} = N_{L'/K'} ∘ ideleClassEquiv eL`. -/
theorem ideleClassEquiv_normClassHom (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x))
    (z : IdeleClassGroup L) :
    ideleClassEquiv eK (IdeleClassGroup.normClassHom K L z) =
      IdeleClassGroup.normClassHom K' L' (ideleClassEquiv eL z) := by
  obtain ⟨y, rfl⟩ := IdeleClassGroup.mk_surjective L z
  rw [IdeleClassGroup.normClassHom_mk, ideleClassEquiv_mk, ideleClassEquiv_mk,
    IdeleClassGroup.normClassHom_mk]
  congr 1
  exact ideleEquiv_normIdeleHom eK eL hcomp y

/-- The idèle class transport carries the norm subgroup `N_{L/K}C_L` into `N_{L'/K'}C_{L'}`. -/
theorem normClassSubgroup_map_le (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x)) :
    (Idele.normClassSubgroup K L).map (ideleClassEquiv eK).toMonoidHom ≤
      Idele.normClassSubgroup K' L' := by
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  rw [Idele.mem_normClassSubgroup] at hq
  obtain ⟨z, rfl⟩ := hq
  change ideleClassEquiv eK (IdeleClassGroup.normClassHom K L z) ∈
    Idele.normClassSubgroup K' L'
  rw [ideleClassEquiv_normClassHom eK eL hcomp]
  exact Idele.mem_normClassSubgroup.mpr ⟨_, rfl⟩

/-- **The idèle class transport maps the norm subgroup onto the norm subgroup.** -/
theorem normClassSubgroup_map_ideleClassEquiv (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x)) :
    (Idele.normClassSubgroup K L).map (ideleClassEquiv eK).toMonoidHom =
      Idele.normClassSubgroup K' L' := by
  refine le_antisymm (normClassSubgroup_map_le eK eL hcomp) ?_
  intro y hy
  rw [Subgroup.mem_map]
  obtain ⟨q', hq'⟩ := Idele.mem_normClassSubgroup.mp hy
  refine ⟨IdeleClassGroup.normClassHom K L ((ideleClassEquiv eL).symm q'), ?_, ?_⟩
  · exact Idele.mem_normClassSubgroup.mpr ⟨_, rfl⟩
  · change ideleClassEquiv eK
        (IdeleClassGroup.normClassHom K L ((ideleClassEquiv eL).symm q')) = y
    rw [ideleClassEquiv_normClassHom eK eL hcomp, MulEquiv.apply_symm_apply, hq']

/-- **The norm index is invariant under ring equivalences of number fields.** -/
theorem normClassSubgroup_index_eq (eK : K ≃+* K') (eL : L ≃+* L')
    (hcomp : ∀ x : K, eL (algebraMap K L x) = algebraMap K' L' (eK x)) :
    (Idele.normClassSubgroup K L).index = (Idele.normClassSubgroup K' L').index := by
  have h := normClassSubgroup_map_ideleClassEquiv eK eL hcomp
  rw [← h]
  exact (Subgroup.index_map_equiv (Idele.normClassSubgroup K L) (ideleClassEquiv eK)).symm

end NK.GlobalCFTdeep.Transport
