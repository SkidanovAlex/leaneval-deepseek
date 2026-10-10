import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.ExtH1Iso
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open SSGRoute.PTExt

namespace Work.SSGRoute
namespace ExtH1

/-!
# Coefficient naturality of the degree-one bridge `H¹(G,M) ≅ Ext¹_G(ℤ,M)`

This file proves `Work.SSGRoute.gammaHom_natural_coeff`: for a `G`-equivariant additive map
`f : M →+ N` (with `F : modRep G M ⟶ modRep G N` the induced morphism of representations),

  `gammaHom G N hS (mapH1 G f hf y) = (gammaHom G M hS y).comp (mk₀ F) (add_zero 1)`.

The proof is the standard two-step reduction.

* On `1`-cocycles: the derivation bridge satisfies
  `cocycleHom (f ∘ ψ) = cocycleHom ψ ≫ F` (`cocycleHom_mapZ1_eq`), because both sides send
  `γ - 1` to `f (ψ γ)`.
* On `Ext¹`: Yoneda associativity (`Abelian.Ext.comp_assoc_of_third_deg_zero`) and
  `Abelian.Ext.mk₀_comp_mk₀` turn this into the statement that `Φ` is compatible with
  post-composition by `mk₀ F` (`gammaZ1_natural`).
-/

variable (G : Type) [Group G]

/-- Computation rule for the connecting map `phiMap`. -/
theorem phiMap_apply (M : Type) [AddCommGroup M] [DistribMulAction G M]
    [SMulCommClass G Coeff M] (hS : (augSES G).ShortExact) (g : augI G ⟶ modRep G M) :
    phiMap G M hS g = hS.extClass.comp (Abelian.Ext.mk₀ g) (by norm_num : 1 + 0 = 1) := rfl

/-- The underlying function of `mapZ1` is application of `f`. -/
theorem mapZ1_apply (M N : Type) [AddCommGroup M] [DistribMulAction G M]
    [SMulCommClass G Coeff M] [AddCommGroup N] [DistribMulAction G N] [SMulCommClass G Coeff N]
    (f : M →+ N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (ψ : ↥(Work.GroupCohomology.Z1 G M)) (g : G) :
    ((Work.GroupCohomology.mapZ1 G f hf ψ : Work.GroupCohomology.Z1 G N) : G → N) g
      = f (ψ.1 g) := by
  rw [Work.GroupCohomology.mapZ1_coe, Work.GroupCohomology.mapCochain1_apply]

/-- **Cocycle-level coefficient naturality** of the derivation bridge: pushing the crossed
homomorphism `φ` forward along `f` and then bridging to `I_G ⟶ N` is the same as bridging first
and post-composing with `F`. -/
theorem cocycleHom_comp_coeff (M N : Type) [AddCommGroup M] [DistribMulAction G M]
    [SMulCommClass G Coeff M] [AddCommGroup N] [DistribMulAction G N] [SMulCommClass G Coeff N]
    (f : M →+ N) (F : modRep G M ⟶ modRep G N) (hF : ∀ m : M, F.hom m = f m)
    (φ : G → M) (hφ : IsCrossedHom (G := G) (M := M) φ)
    (hφ' : IsCrossedHom (G := G) (M := N) (fun g => f (φ g))) :
    cocycleHom (G := G) (M := N) (fun g => f (φ g)) hφ' =
      cocycleHom (G := G) (M := M) φ hφ ≫ F := by
  apply hom_ext_augDiff G N
  intro γ
  rw [Rep.hom_comp, Representation.IntertwiningMap.comp_apply, cocycleHom_augDiff,
    cocycleHom_augDiff]
  exact (hF (φ γ)).symm

/-- `mk₀`-composition in the `add_zero` normalisation used by `Ext.comp`. -/
theorem mk₀_comp_mk₀_addZero {X Y Z : Rep.{0} Coeff G} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Abelian.Ext.mk₀ f).comp (Abelian.Ext.mk₀ g) (add_zero 0) = Abelian.Ext.mk₀ (f ≫ g) := by
  rw [show (add_zero 0 : (0 : ℕ) + 0 = 0) = (zero_add 0 : (0 : ℕ) + 0 = 0) from
    Subsingleton.elim _ _]
  exact Abelian.Ext.mk₀_comp_mk₀ f g

/-- Cocycle-level naturality in the `mapZ1` normalisation used by `gammaZ1`. -/
theorem cocycleHom_mapZ1_eq (M N : Type) [AddCommGroup M] [DistribMulAction G M]
    [SMulCommClass G Coeff M] [AddCommGroup N] [DistribMulAction G N] [SMulCommClass G Coeff N]
    (f : M →+ N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (F : modRep G M ⟶ modRep G N) (hF : ∀ m : M, F.hom m = f m)
    (ψ : ↥(Work.GroupCohomology.Z1 G M)) :
    cocycleHom (G := G) (M := N) ((Work.GroupCohomology.mapZ1 G f hf ψ).1)
        ((crossedHom_iff (G := G) (M := N) ((Work.GroupCohomology.mapZ1 G f hf ψ).1)).mp
          (Work.GroupCohomology.mapZ1 G f hf ψ).2) =
      cocycleHom (G := G) (M := M) ψ.1
        ((crossedHom_iff (G := G) (M := M) ψ.1).mp ψ.2) ≫ F := by
  apply hom_ext_augDiff G N
  intro γ
  rw [Rep.hom_comp, Representation.IntertwiningMap.comp_apply, cocycleHom_augDiff,
    cocycleHom_augDiff, mapZ1_apply G M N f hf ψ γ]
  exact (hF (ψ.1 γ)).symm

/-- **Coefficient naturality of `gammaZ1`** (the bridge on `1`-cocycles). -/
theorem gammaZ1_natural (M N : Type) [AddCommGroup M] [DistribMulAction G M]
    [SMulCommClass G Coeff M] [AddCommGroup N] [DistribMulAction G N] [SMulCommClass G Coeff N]
    (hS : (augSES G).ShortExact) (f : M →+ N)
    (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (F : modRep G M ⟶ modRep G N) (hF : ∀ m : M, F.hom m = f m)
    (ψ : ↥(Work.GroupCohomology.Z1 G M)) :
    gammaZ1 G N hS (Work.GroupCohomology.mapZ1 G f hf ψ) =
      (gammaZ1 G M hS ψ).comp (Abelian.Ext.mk₀ F) (add_zero 1) := by
  simp only [gammaZ1_apply, phiMap_apply]
  rw [cocycleHom_mapZ1_eq G M N f hf F hF ψ]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [mk₀_comp_mk₀_addZero]

end ExtH1

/-- **Coefficient naturality of the degree-one bridge `H¹(G,M) ≅ Ext¹_G(ℤ,M)`** (node `E0b` at
`n = 1`, `Submission/Work/SSGRoute/ExtH1Iso.lean`).  A `G`-equivariant additive map `f : M →+ N`
induces `mapH1 G f hf : H¹(G,M) → H¹(G,N)`; pushing a class forward along `f` and then applying
the bridge is the same as applying the bridge first and composing with the class `mk₀ F` of the
induced morphism of representations `F : modRep G M ⟶ modRep G N`.

Intended route: reduce `y` to `H1π ψ` using `QuotientAddGroup.mk'_surjective`, then rewrite with
`Work.GroupCohomology.mapH1_H1π`, `Work.SSGRoute.ExtH1.gammaHom_H1π`,
`Work.SSGRoute.ExtH1.gammaZ1_apply`, reducing to the cocycle-level identity
`cocycleHom (f ∘ ψ.1) = cocycleHom ψ.1 ≫ F` in `augI G ⟶ modRep G N`.  That is proved with
`Work.SSGRoute.ExtH1.hom_ext_augDiff` + `Work.SSGRoute.ExtH1.cocycleHom_augDiff` + `hF`; the
crossed-homomorphism condition for `f ∘ ψ.1` follows from that of `ψ.1` and `hf` (use
`Work.SSGRoute.ExtH1.crossedHom_iff` to move between the two conventions, and
`Work.GroupCohomology.mapZ1_coe`/`mapCochain1_apply` to identify `(mapZ1 G f hf ψ).1`).
The `Ext`-level step is `Abelian.Ext.mk₀_comp_mk₀` plus `Abelian.Ext.comp_assoc_of_third_deg_zero`
applied to `hS.extClass`, `mk₀ (cocycleHom ψ.1)` and `mk₀ F`.  The template is
`Work.SSGRoute.ExtH1.phiMap_cocycleHom_add` in `ExtH1Iso.lean`. -/
theorem gammaHom_natural_coeff (G : Type) [Group G] (M N : Type) [AddCommGroup M]
    [DistribMulAction G M] [SMulCommClass G Coeff M] [AddCommGroup N] [DistribMulAction G N]
    [SMulCommClass G Coeff N] (hS : (Work.SSGRoute.ExtH1.augSES G).ShortExact)
    (f : M →+ N) (hf : ∀ (g : G) (m : M), f (g • m) = g • f m)
    (F : modRep G M ⟶ modRep G N) (hF : ∀ m : M, F.hom m = f m)
    (y : Work.GroupCohomology.H1 G M) :
    Work.SSGRoute.ExtH1.gammaHom G N hS (Work.GroupCohomology.mapH1 G f hf y) =
      (Work.SSGRoute.ExtH1.gammaHom G M hS y).comp (Abelian.Ext.mk₀ F) (add_zero 1) := by
  induction y using Work.GroupCohomology.H1_induction_on with
  | h ψ =>
    rw [Work.GroupCohomology.mapH1_H1π]
    rw [Work.SSGRoute.ExtH1.gammaHom_H1π]
    rw [Work.SSGRoute.ExtH1.gammaHom_H1π]
    exact Work.SSGRoute.ExtH1.gammaZ1_natural G M N hS f hf F hF ψ

end Work.SSGRoute
