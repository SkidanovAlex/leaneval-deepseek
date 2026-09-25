import Submission.NK.GlobalCFTdeep.Transport.IdeleEquiv

/-!
# Transport of the idèle class group along a ring equivalence

The idèle transport `ideleEquiv e : 𝕀 K ≃* 𝕀 K'` of `Transport/IdeleEquiv.lean` maps the
principal idèles `Kˣ` onto the principal idèles `K'ˣ`, hence descends to an isomorphism
`C_K ≃* C_{K'}` of the idèle class groups.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFTdeep.Transport

open NK.GlobalCFT

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']

/-- The idèle transport maps the subgroup of principal idèles onto the subgroup of principal
idèles. -/
theorem principalSubgroup_map_ideleEquiv (e : K ≃+* K') :
    (Idele.principalSubgroup K).map (ideleEquiv e).toMonoidHom = Idele.principalSubgroup K' := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Idele.mem_principalSubgroup] at hy ⊢
    obtain ⟨a, rfl⟩ := hy
    exact ⟨Units.map (e : K →* K') a, (ideleEquiv_principalIdele e a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨Idele.principalIdele K (Units.map (e.symm : K' →* K) b), ?_, ?_⟩
    · rw [Idele.mem_principalSubgroup]; exact ⟨_, rfl⟩
    · change ideleEquiv e (Idele.principalIdele K (Units.map (e.symm : K' →* K) b)) =
        Idele.principalIdele K' b
      rw [ideleEquiv_principalIdele]
      congr 1
      ext y
      simp

/-- **Transport of the idèle class group along a ring equivalence of number fields**:
`C_K ≃* C_{K'}`. -/
noncomputable def ideleClassEquiv (e : K ≃+* K') : IdeleClassGroup K ≃* IdeleClassGroup K' :=
  QuotientGroup.congr _ _ (ideleEquiv e) (principalSubgroup_map_ideleEquiv e)

@[simp] theorem ideleClassEquiv_mk (e : K ≃+* K') (x : Idele K) :
    ideleClassEquiv e (IdeleClassGroup.mk K x) =
      IdeleClassGroup.mk K' (ideleEquiv e x) :=
  QuotientGroup.congr_mk _ _ _ _ x

end NK.GlobalCFTdeep.Transport
