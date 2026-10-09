/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFT.GaloisIdelesAction
import Submission.NK.GlobalCFT.Galois.globalCFT_one_smul_idele
import Submission.NK.GlobalCFT.Galois.globalCFT_mul_smul_idele
import Submission.NK.GlobalCFT.Galois.globalCFT_smul_idele_mul
import Submission.NK.GlobalCFT.Galois.globalCFT_smul_principalIdele
import Submission.NK.GlobalCFT.IdeleClassGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Galois action on the idèle class group

`Gal(L/K) = (L ≃ₐ[K] L)` acts on `𝕀 L` by `(σ · x)_w = σ_*(x_{σ⁻¹ w})`; this action is
compatible with multiplication and hence is a `MulDistribMulAction`.  Since it permutes the
principal idèles (`σ · (y) = (σ y)`), it descends to the idèle class group `C_L`, making `C_L` a
`Gal(L/K)`-module — the input for the cohomological formulation of the class formation axioms.

## Main definitions

* `NK.GlobalCFT.Idele.instMulDistribMulAction`: `Gal(L/K)` acts on `𝕀 L` by group
  automorphisms.
* `NK.GlobalCFT.IdeleClassGroup` action of `Gal(L/K)` on `C_L`.

## Main results

* `NK.GlobalCFT.Idele.smul_principalSubgroup_le`: the action preserves the principal idèles.
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

instance : MulAction (L ≃ₐ[K] L) (Idele L) where
  one_smul := NK.GlobalCFT.Galois.globalCFT_one_smul_idele
  mul_smul := NK.GlobalCFT.Galois.globalCFT_mul_smul_idele

instance : MulDistribMulAction (L ≃ₐ[K] L) (Idele L) where
  smul_mul := NK.GlobalCFT.Galois.globalCFT_smul_idele_mul
  smul_one σ := by
    ext w
    simp [smul_apply]

/-- The action of `Gal(L/K)` preserves the principal idèles. -/
theorem smul_mem_principalSubgroup {σ : L ≃ₐ[K] L} {x : Idele L}
    (hx : x ∈ principalSubgroup L) : σ • x ∈ principalSubgroup L := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨Units.map σ.toMonoidHom y,
    (NK.GlobalCFT.Galois.globalCFT_smul_principalIdele σ y).symm⟩

/-- The action of `Gal(L/K)` preserves the equivalence relation defining `C_L`: if `x` and `y`
differ by a principal idèle, so do `σ · x` and `σ • y`. -/
theorem mul_smul_mem_principalSubgroup {σ : L ≃ₐ[K] L} {x y : Idele L}
    (h : x⁻¹ * y ∈ principalSubgroup L) : (σ • x)⁻¹ * (σ • y) ∈ principalSubgroup L := by
  have h' : (σ • x)⁻¹ * (σ • y) = σ • (x⁻¹ * y) := by
    have h1 : σ • x⁻¹ = (σ • x)⁻¹ :=
      (MulDistribMulAction.toMulAut (L ≃ₐ[K] L) (Idele L) σ).map_inv x
    rw [← h1, ← MulDistribMulAction.smul_mul]
  rw [h']
  exact smul_mem_principalSubgroup h

end Idele

namespace IdeleClassGroup

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- `Gal(L/K)` acts on the idèle class group `C_L`, by transport of the action on `𝕀 L`. -/
noncomputable instance : SMul (L ≃ₐ[K] L) (IdeleClassGroup L) where
  smul σ := Quotient.map (fun x => σ • x) (by
    intro x y hxy
    exact QuotientGroup.leftRel_apply.mpr
      (Idele.mul_smul_mem_principalSubgroup (QuotientGroup.leftRel_apply.mp hxy)))

/-- The action on `C_L` is induced by the action on `𝕀 L`. -/
theorem smul_mk (σ : L ≃ₐ[K] L) (x : Idele L) :
    σ • IdeleClassGroup.mk L x = IdeleClassGroup.mk L (σ • x) := rfl

instance : MulAction (L ≃ₐ[K] L) (IdeleClassGroup L) where
  one_smul q := by
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L q
    rw [smul_mk, NK.GlobalCFT.Galois.globalCFT_one_smul_idele]
  mul_smul σ σ' q := by
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L q
    rw [smul_mk, smul_mk, smul_mk, NK.GlobalCFT.Galois.globalCFT_mul_smul_idele]

instance : MulDistribMulAction (L ≃ₐ[K] L) (IdeleClassGroup L) where
  smul_mul σ q q' := by
    obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L q
    obtain ⟨y, rfl⟩ := IdeleClassGroup.mk_surjective L q'
    rw [← map_mul, smul_mk, smul_mk, smul_mk, MulDistribMulAction.smul_mul, map_mul]
  smul_one σ := by
    rw [← map_one (IdeleClassGroup.mk L), smul_mk, MulDistribMulAction.smul_one, map_one]

end IdeleClassGroup

end NK.GlobalCFT
