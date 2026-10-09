/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The idèles as a Galois representation; the principal idèles and the class-group quotient

Umbrella development: `Submission/Work/HassePrinciple/` (README §8.4 item 2, §12.4).

This file provides the *coefficient* layer of item 2 of README §8.4 (Shapiro's lemma for the
idèles) in this chapter's universe and coefficient conventions (`CoeffInt = ULift ℤ`, matching
`NK.HassePrinciple.muRep`/`unitsRep`):

* `NK.HassePrinciple.ideleRep` — the idèle group `𝕀_L` as a `CoeffInt`-linear representation of
  `Gal(L/K)`, with the computation rule `ideleRep_ρ_apply`;
* `NK.HassePrinciple.classGroupRep` — the idèle class group `C_L` likewise;
* `NK.HassePrinciple.ideleIncl` and `NK.HassePrinciple.classGroupMap` — the principal idèles
  `Lˣ ↪ 𝕀_L` and the quotient `𝕀_L ↠ C_L` as morphisms of `CoeffInt`-linear representations, with
  `ideleIncl_comp_classGroupMap : ideleIncl ≫ classGroupMap = 0`;
* (next stretch) the short exactness of `0 → Lˣ → 𝕀_L → C_L → 0` and the long exact sequence
  consequence `H¹(Γ, C_L) = 0 ⟹ H²(Γ, Lˣ) ↪ H²(Γ, 𝕀_L)`.

The two statements of item 2 that are built on this layer are

* `NK.HassePrinciple.subsingleton_groupCohomology_one_ideleRep` — `H¹(Gal(L/K), 𝕀_L) = 0`
  (Shapiro's lemma for the idèles together with Hilbert 90 at the places);
* `NK.HassePrinciple.injective_h2_units_ideleRep_of_subsingleton_h1` — the edge map
  `H²(Gal(L/K), Lˣ) → H²(Gal(L/K), 𝕀_L)` is injective as soon as `H¹(Gal(L/K), C_L) = 0` (the long
  exact sequence of `0 → Lˣ → 𝕀_L → C_L → 0`); the hypothesis holds for `p`-group level groups by
  `NK.HassePrinciple.subsingleton_groupCohomology_one_ideleClassGroup_of_isPGroup`.

Together with the idèle localisation `H^n(Γ, 𝕀_L) ≅ ∏_w H^n(Γ_w, L_wˣ)` this yields the *relative*
Hasse–Brauer–Noether theorem `H²(Γ, Lˣ) ↪ ∏_w H²(Γ_w, L_wˣ)`, i.e. the form of the Hasse principle
that the classical theory produces from the Hasse norm theorem (README §12.3, item (e)).
-/

import Mathlib
import Submission.NK.GlobalCFT.GlobalCFT
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
