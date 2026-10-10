import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Submission.NK.GlobalCFT.ClassFormation.globalCFT_fieldAxiom_self
import Submission.NK.GlobalCFT.H0Computation
import Submission.NK.GlobalCFT.IdeleClassGroup.globalCFT_compactSpace_normOneClassGroup
import Submission.NK.GlobalCFT.IdeleClassGroupExact
import Submission.NK.GlobalCFT.Ideles.globalCFT_principalIdele_injective
import Submission.NK.GlobalCFT.Ideles.globalCFT_principalSubgroup_isClosed
import Submission.NK.HassePrinciple.Mu
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory Representation
open NK.GlobalCFT

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace NK.HassePrinciple

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The idèle group `𝕀_L`** as a `CoeffInt`-linear representation of `Gal(L/K)`. -/
noncomputable def ideleRep (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : Rep CoeffInt (L ≃ₐ[K] L) :=
  Rep.ofDistribMulAction CoeffInt (L ≃ₐ[K] L) (Additive (Idele L))

/-- **The idèle class group `C_L`** as a `CoeffInt`-linear representation of `Gal(L/K)`. -/
noncomputable def classGroupRep (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : Rep CoeffInt (L ≃ₐ[K] L) :=
  Rep.ofDistribMulAction CoeffInt (L ≃ₐ[K] L) (Additive (IdeleClassGroup L))

/-- The action of `Gal(L/K)` on the idèles is the one of `NK.GlobalCFT.Idele`. -/
theorem ideleRep_ρ_apply (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (σ : L ≃ₐ[K] L) (x : Idele L) :
    (ideleRep K L).ρ σ (Additive.ofMul x) = Additive.ofMul (σ • x) := rfl

/-- The action of `Gal(L/K)` on the idèle class group is the one of
`NK.GlobalCFT.IdeleClassGroup`. -/
theorem classGroupRep_ρ_apply (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (σ : L ≃ₐ[K] L) (q : IdeleClassGroup L) :
    (classGroupRep K L).ρ σ (Additive.ofMul q) = Additive.ofMul (σ • q) := rfl


/-- **The principal idèles `Lˣ ↪ 𝕀_L`** as a morphism of `CoeffInt`-linear representations: the
underlying map is `x ↦ Idele.principalIdele L x`. -/
noncomputable def ideleIncl (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : unitsRep K L ⟶ ideleRep K L :=
  Rep.ofHom
    { toFun := fun x => Additive.ofMul (Idele.principalIdele L (Additive.toMul x))
      map_add' := fun x y => by
        change Additive.ofMul (Idele.principalIdele L (Additive.toMul x * Additive.toMul y)) =
          Additive.ofMul (Idele.principalIdele L (Additive.toMul x)) +
            Additive.ofMul (Idele.principalIdele L (Additive.toMul y))
        rw [map_mul]
        rfl
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        show Additive.ofMul (Idele.principalIdele L ((Additive.toMul x) ^ z)) =
          Additive.ofMul ((Idele.principalIdele L (Additive.toMul x)) ^ z)
        rw [map_zpow]
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        change Additive.ofMul (Idele.principalIdele L (Additive.toMul
              (((ofDistribMulAction CoeffInt.{u} (L ≃ₐ[K] L) (Additive Lˣ)) σ) x)))
          = ((ofDistribMulAction CoeffInt.{u} (L ≃ₐ[K] L) (Additive (Idele L))) σ)
              (Additive.ofMul (Idele.principalIdele L (Additive.toMul x)))
        have hunits : ((ofDistribMulAction CoeffInt.{u} (L ≃ₐ[K] L) (Additive Lˣ)) σ) x =
            Additive.ofMul (Units.map σ.toMonoidHom (Additive.toMul x)) := rfl
        rw [hunits]
        rw [show Additive.toMul (Additive.ofMul (Units.map σ.toMonoidHom (Additive.toMul x)))
            = Units.map σ.toMonoidHom (Additive.toMul x) from rfl]
        rw [show ((ofDistribMulAction CoeffInt.{u} (L ≃ₐ[K] L) (Additive (Idele L))) σ)
              (Additive.ofMul (Idele.principalIdele L (Additive.toMul x)))
            = Additive.ofMul (σ • Idele.principalIdele L (Additive.toMul x)) from rfl]
        rw [NK.GlobalCFT.Galois.globalCFT_smul_principalIdele] }

/-- Computation rule for `ideleIncl`. -/
@[simp]
theorem ideleIncl_apply (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (x : Lˣ) :
    (ideleIncl K L).hom (Additive.ofMul x) = Additive.ofMul (Idele.principalIdele L x) := rfl

/-- **The quotient `𝕀_L ↠ C_L`** as a morphism of `CoeffInt`-linear representations. -/
noncomputable def classGroupMap (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] : ideleRep K L ⟶ classGroupRep K L :=
  Rep.ofHom
    { toFun := fun x => Additive.ofMul (IdeleClassGroup.mk L (Additive.toMul x))
      map_add' := fun x y => by
        change Additive.ofMul (IdeleClassGroup.mk L (Additive.toMul x * Additive.toMul y)) =
          Additive.ofMul (IdeleClassGroup.mk L (Additive.toMul x)) +
            Additive.ofMul (IdeleClassGroup.mk L (Additive.toMul y))
        rw [map_mul]
        rfl
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        show Additive.ofMul (IdeleClassGroup.mk L ((Additive.toMul x) ^ z)) =
          Additive.ofMul ((IdeleClassGroup.mk L (Additive.toMul x)) ^ z)
        rw [map_zpow]
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        change Additive.ofMul (IdeleClassGroup.mk L (Additive.toMul
              (((ofDistribMulAction CoeffInt.{u} (L ≃ₐ[K] L) (Additive (Idele L))) σ) x)))
          = ((ofDistribMulAction CoeffInt.{u} (L ≃ₐ[K] L) (Additive (IdeleClassGroup L))) σ)
              (Additive.ofMul (IdeleClassGroup.mk L (Additive.toMul x)))
        have hidele : ((ofDistribMulAction CoeffInt.{u} (L ≃ₐ[K] L) (Additive (Idele L))) σ) x =
            Additive.ofMul (σ • Additive.toMul x) := rfl
        rw [hidele]
        rw [show Additive.toMul (Additive.ofMul (σ • Additive.toMul x)) = σ • Additive.toMul x
          from rfl]
        rw [show ((ofDistribMulAction CoeffInt.{u} (L ≃ₐ[K] L) (Additive (IdeleClassGroup L))) σ)
              (Additive.ofMul (IdeleClassGroup.mk L (Additive.toMul x)))
            = Additive.ofMul (σ • IdeleClassGroup.mk L (Additive.toMul x)) from rfl]
        rw [IdeleClassGroup.smul_mk] }

/-- Computation rule for `classGroupMap`. -/
@[simp]
theorem classGroupMap_apply (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (x : Idele L) :
    (classGroupMap K L).hom (Additive.ofMul x) =
      Additive.ofMul (IdeleClassGroup.mk L x) := rfl

/-- **The principal idèles are killed by the quotient map**: `ideleIncl ≫ classGroupMap = 0`. -/
theorem ideleIncl_comp_classGroupMap (K L : Type u) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] :
    ideleIncl K L ≫ classGroupMap K L = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change Additive.ofMul (IdeleClassGroup.mk L (Idele.principalIdele L (Additive.toMul x)))
    = Additive.ofMul 1
  rw [show IdeleClassGroup.mk L (Idele.principalIdele L (Additive.toMul x)) = 1 from
    (QuotientGroup.eq_one_iff _).mpr ⟨Additive.toMul x, rfl⟩]

end NK.HassePrinciple
