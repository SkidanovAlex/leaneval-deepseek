/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFT.NormGroup
import Submission.NK.GlobalCFT.Norm.globalCFT_eventually_normIdeleFun_mem
import Submission.NK.GlobalCFT.Norm.globalCFT_normIdeleFun_principalIdele
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm as a homomorphism of idèles

Packaging the componentwise formula `NK.GlobalCFT.Idele.normIdeleFun` with the
eventual-membership lemma `globalCFT_eventually_normIdeleFun_mem`, we obtain the norm
`N_{L/K} : 𝕀 L →* 𝕀 K`.

## Main definitions

* `NK.GlobalCFT.Idele.normIdeleHom`: the idèlic norm.

## Main results

* `NK.GlobalCFT.Idele.normImage_eq_map`: the norm subgroup `N_{L/K} 𝕀 L` is the image of the
  norm homomorphism.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT

namespace Idele

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- The **norm** `N_{L/K} : 𝕀 L →* 𝕀 K` on idèles, given by the componentwise formula
`N(x)_v = ∏_{w | v} N_{L_w/K_v}(x_w)`. -/
def normIdeleHom (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Idele L →* Idele K where
  toFun x := ⟨fun v => normIdeleFun K L x v, Norm.globalCFT_eventually_normIdeleFun_mem x⟩
  map_one' := ext fun v => normIdeleFun_one_apply v
  map_mul' x y := ext fun v => Norm.globalCFT_normIdeleFun_mul x y v

@[simp] theorem normIdeleHom_apply (x : Idele L) (v : Place K) :
    normIdeleHom K L x v = normIdeleFun K L x v := rfl

/-- The norm subgroup `N_{L/K} 𝕀 L` is the image of the norm homomorphism. -/
theorem normImage_eq_map (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] :
    normImage K L = (normIdeleHom K L).range := by
  ext x
  rw [mem_normImage, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, ext fun v => (hy v).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, fun v => rfl⟩

/-- The idèlic norm of a principal idèle is the principal idèle of the field norm. -/
theorem normIdeleHom_principalIdele (y : Lˣ) :
    normIdeleHom K L (principalIdele L y) =
      principalIdele K (Units.map (Algebra.norm K) y) :=
  ext fun v => NK.GlobalCFT.Norm.globalCFT_normIdeleFun_principalIdele y v

/-- The principal idèles of `L` are killed by the composite `𝕀 L → 𝕀 K → C K`. -/
theorem principalSubgroup_le_ker_normMk (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    principalSubgroup L ≤ ((IdeleClassGroup.mk K).comp (normIdeleHom K L)).ker := by
  rintro y ⟨z, rfl⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, normIdeleHom_principalIdele]
  exact (QuotientGroup.eq_one_iff (Idele.principalIdele K (Units.map (Algebra.norm K) z))).mpr
    ⟨_, rfl⟩

end Idele

namespace IdeleClassGroup

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- The **norm** `N_{L/K} : C_L →* C_K` on idèle class groups. -/
def normClassHom (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : IdeleClassGroup L →* IdeleClassGroup K :=
  QuotientGroup.lift (Idele.principalSubgroup L)
    ((IdeleClassGroup.mk K).comp (Idele.normIdeleHom K L))
    (Idele.principalSubgroup_le_ker_normMk K L)

@[simp] theorem normClassHom_mk (x : Idele L) :
    normClassHom K L (IdeleClassGroup.mk L x) = IdeleClassGroup.mk K (Idele.normIdeleHom K L x) :=
  QuotientGroup.lift_mk' _ _ x

end IdeleClassGroup

end NK.GlobalCFT
