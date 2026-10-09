/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleInclusion_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_exists
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective
import Submission.NK.GlobalCFT.Inclusion.globalCFT_invariants_ideleClassGroup
import Submission.NK.GlobalCFT.Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom
import Submission.NK.GlobalCFT.Cohomology.globalCFT_H0Computation_of_invariants_and_norm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `H⁰`-computation for the idèle class group

This file assembles the **`H⁰`-computation** of global class field theory (Milne, *Class Field
Theory*, Lemma 4.1): for a finite Galois extension `L / K`,

  `C_K ⧸ N_{L/K} C_L ≅ Ĥ⁰(Gal(L/K), C_L)`,

i.e. the natural map `C_K → C_L` identifies `C_K` with the Galois invariants of `C_L` and carries
the norm subgroup `N_{L/K} C_L` onto the image of the norm map.  The ingredients are

* the inclusion of idèles `𝕀 K →* 𝕀 L` and its descent `ψ : C_K →* C_L`
  (`Inclusion.globalCFT_ideleInclusion_exists`, `..._ideleClassGroup_inclusion_exists`),
* `ψ` is injective (`Inclusion.globalCFT_ideleClassGroup_inclusion_injective`),
* the invariants are the image of `ψ` (`Inclusion.globalCFT_invariants_ideleClassGroup`),
* the norm is the product of the conjugates
  (`Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom`),

combined by `NK.GlobalCFT.Cohomology.globalCFT_H0Computation_of_invariants_and_norm`.

Everything here is unconditional (no hypothesis is assumed).  The fields are in `Type 0` because
Mathlib's `tateCohomology` ties the universes of the coefficient ring and the group.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.GlobalCFT

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The norm is the product of the conjugates**, at the level of idèle classes: for the
inclusion `ψ : C_K →* C_L` and `q ∈ C_L` one has `ψ(N_{L/K} q) = ∏_{σ} σ · q`. -/
theorem globalCFT_normClassHom_eq_prod_smul
    (u : Place L → Place K) (hu : ∀ w : Place L, Place.LiesOver w (u w))
    (φ : 𝕀[K] →* 𝕀[L])
    (hφ : ∀ (x : 𝕀[K]) (w : Place L),
      φ x w = Place.localAlgebraMapUnits w (u w) (hu w) (x (u w)))
    (ψ : C[K] →* C[L])
    (hψ : ∀ x : 𝕀[K], ψ (IdeleClassGroup.mk K x) = IdeleClassGroup.mk L (φ x))
    (q : C[L]) :
    ψ (IdeleClassGroup.normClassHom K L q) = ∏ σ : L ≃ₐ[K] L, σ • q := by
  obtain ⟨x, rfl⟩ := IdeleClassGroup.mk_surjective L q
  rw [IdeleClassGroup.normClassHom_mk, hψ,
    ← Inclusion.globalCFT_prod_smul_eq_inclusion_normIdeleHom u hu φ hφ x, map_prod]
  exact Finset.prod_congr rfl fun σ _ => (IdeleClassGroup.smul_mk σ x).symm

/-- **The `H⁰`-computation** (Milne, *CFT*, Lemma 4.1), unconditionally: for a finite Galois
extension `L / K` of number fields, the idèle class group `C_K` is the Galois invariant part of
`C_L` modulo the norm subgroup, i.e. there is an isomorphism
`C_K ⧸ N_{L/K} C_L ≅ Ĥ⁰(Gal(L/K), C_L)`. -/
theorem globalCFT_H0Computation : H0Computation K L := by
  classical
  obtain ⟨φ, hφ⟩ := Inclusion.globalCFT_ideleInclusion_exists (K := K) (L := L)
    (fun w => Classical.choose (Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w))
    (fun w => Classical.choose_spec (Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w))
  obtain ⟨ψ, hψ⟩ :=
    Inclusion.globalCFT_ideleClassGroup_inclusion_exists (K := K) (L := L) _ _ φ hφ
  exact Cohomology.globalCFT_H0Computation_of_invariants_and_norm (K := K) (L := L) ψ
    (Inclusion.globalCFT_ideleClassGroup_inclusion_injective (K := K) (L := L) _ _ φ hφ ψ hψ)
    (fun q => Inclusion.globalCFT_invariants_ideleClassGroup (K := K) (L := L) _ _ φ hφ ψ hψ q)
    (fun q => globalCFT_normClassHom_eq_prod_smul (K := K) (L := L) _ _ φ hφ ψ hψ q)

end NK.GlobalCFT
