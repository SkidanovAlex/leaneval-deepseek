/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFT.Norm
import Submission.NK.GlobalCFT.Norm.globalCFT_normIdeleFun_mul
import Submission.NK.GlobalCFT.Norm.globalCFT_normIdeleFun_one

/-!
# The norm of idèles and idèle classes, packaged

Building on the componentwise formula `NK.GlobalCFT.Idele.normIdeleFun`, this file contains

* `NK.GlobalCFT.Idele.normImage`: the norm subgroup `N_{L/K} 𝕀 L ≤ 𝕀 K`,
* `NK.GlobalCFT.Idele.normClassSubgroup`: the norm subgroup `N_{L/K} C_L ≤ C_K`.

The packaged homomorphisms `normIdeleHom : 𝕀 L →* 𝕀 K` and `normClassHom : C L →* C K` are in
`NK.GlobalCFT.NormFunctorial`, which uses the eventual-membership lemma
`globalCFT_eventually_normIdeleFun_mem` and the compatibility with principal idèles.
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

/-- The norm formula sends the idèle `1` to `1`. -/
theorem normIdeleFun_one_apply (v : Place K) : normIdeleFun K L 1 v = 1 :=
  Norm.globalCFT_normIdeleFun_one v

/-- The norm formula is compatible with inverses. -/
theorem normIdeleFun_inv_apply (x : Idele L) (v : Place K) :
    normIdeleFun K L x⁻¹ v = (normIdeleFun K L x v)⁻¹ := by
  have h : normIdeleFun K L x⁻¹ v * normIdeleFun K L x v = 1 := by
    rw [← Norm.globalCFT_normIdeleFun_mul, inv_mul_cancel, normIdeleFun_one_apply]
  exact eq_inv_of_mul_eq_one_left h

/-- The image of the idèle norm `𝕀 L → 𝕀 K`, as a subgroup of `𝕀 K`.  Its elements are exactly
the values of the componentwise norm formula. -/
def normImage (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Subgroup (Idele K) where
  carrier := {x | ∃ y : Idele L, ∀ v, x v = normIdeleFun K L y v}
  one_mem' := ⟨1, fun v => (normIdeleFun_one_apply v).symm⟩
  mul_mem' := by
    rintro x x' ⟨y, hy⟩ ⟨y', hy'⟩
    refine ⟨y * y', fun v => ?_⟩
    rw [mul_apply, hy v, hy' v, ← Norm.globalCFT_normIdeleFun_mul]
  inv_mem' := by
    rintro x ⟨y, hy⟩
    refine ⟨y⁻¹, fun v => ?_⟩
    rw [inv_apply, hy v, normIdeleFun_inv_apply]

theorem mem_normImage {x : Idele K} :
    x ∈ normImage K L ↔ ∃ y : Idele L, ∀ v, x v = normIdeleFun K L y v := Iff.rfl

/-- The **norm subgroup** `N_{L/K} C_L` of the idèle class group of `K`: the image of the norm
subgroup of the idèles in `C_K`. -/
def normClassSubgroup (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] : Subgroup (IdeleClassGroup K) :=
  (normImage K L).map (IdeleClassGroup.mk K)

end Idele

end NK.GlobalCFT
